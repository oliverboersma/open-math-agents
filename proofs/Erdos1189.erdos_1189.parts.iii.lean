import FormalConjectures.ErdosProblems.«1189»

/-!
# Reciprocal sums of irreducible covering sets

The maximum reciprocal sum for an irreducible covering set of size `k` grows as `log k`.
The upper bound follows by numbering the moduli in increasing order. For the lower bound,
we build a chain of periods, extending by a prime at each step. Each modulus introduced at
that step can forbid at most one of the new residue choices. Omitting a modulus therefore
allows us to avoid every remaining class, including the final class modulo the full period.
The first step for each odd prime supplies the harmonic contribution. Additional binary
steps realize every sufficiently large size, and Chebyshev's bounds give logarithmic mass.

The logarithmic order and the prime block construction were published by Star Fleet Math,
whose report credits earlier work of Wouter van Doorn. This formalization proves the covering
and irreducibility properties directly using extensions of congruence classes.
https://www.starfleetmath.com/
-/

namespace OMA.Erdos1189Reciprocal

open Filter Asymptotics

private theorem reciprocal_le_harmonic (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 < n) : ∑ n ∈ S, (n : ℝ)⁻¹ ≤ harmonic S.card := by
  classical
  let e := S.orderEmbOfFin rfl
  have rank_le (i : ℕ) (hi : i < S.card) : i + 1 ≤ e ⟨i, hi⟩ := by
    induction i with
    | zero => exact (hS _ (S.orderEmbOfFin_mem rfl _)).le
    | succ i ih =>
      have hi' : i < S.card := by omega
      have hmono : e ⟨i, hi'⟩ < e ⟨i + 1, hi⟩ := by
        apply e.strictMono
        exact Nat.lt_succ_self i
      have := ih hi'
      omega
  calc
    _ = ∑ i : Fin S.card, ((e i : ℕ) : ℝ)⁻¹ := by
      conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl, Finset.sum_map]
      rfl
    _ ≤ ∑ i : Fin S.card, ((i.val + 1 : ℕ) : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro i _
      apply inv_anti₀ (by positivity)
      exact_mod_cast rank_le i.val i.isLt
    _ = harmonic S.card := by
      simp only [Nat.cast_add, Nat.cast_one]
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => ((n : ℝ) + 1)⁻¹)]
      simp [harmonic, Rat.cast_sum, Rat.cast_inv]

theorem maxReciprocalSum_le_harmonic (k : ℕ) :
    Erdos1189.maxReciprocalSum k ≤ harmonic k := by
  unfold Erdos1189.maxReciprocalSum
  by_cases h : {s : ℝ | ∃ M : Finset ℕ, Erdos1189.IsIrreducibleCoveringSet M ∧ M.card = k ∧
      s = ∑ m ∈ M, (m : ℝ)⁻¹}.Nonempty
  · refine csSup_le h ?_
    rintro _ ⟨M, hM, rfl, rfl⟩
    exact reciprocal_le_harmonic M hM.1.1
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sSup_empty]
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity

theorem maxReciprocalSum_le_log (k : ℕ) :
    Erdos1189.maxReciprocalSum k ≤ 1 + Real.log k :=
  (maxReciprocalSum_le_harmonic k).trans (harmonic_le_one_add_log k)

/-- Each newly available modulus forbids at most one extension of a residue. -/
private theorem single_forbidden_extension {p P m : ℕ} (hp : p.Prime)
    (hm : m ∣ P * p) (hn : ¬ m ∣ P) {x a : ℤ} {i j : Fin p}
    (hi : x + (i.val : ℤ) * P ≡ a [ZMOD m])
    (hj : x + (j.val : ℤ) * P ≡ a [ZMOD m]) : i = j := by
  suffices no_lt : ∀ {u v : Fin p}, u < v →
      (x + (u.val : ℤ) * P ≡ a [ZMOD m]) →
      (x + (v.val : ℤ) * P ≡ a [ZMOD m]) → False by
    rcases lt_trichotomy i j with h | h | h
    · exact (no_lt h hi hj).elim
    · exact h
    · exact (no_lt h hj hi).elim
  intro u v huv hu hv
  have huv' : u.val < v.val := huv
  have hpos : 0 < v.val - u.val := by omega
  have hlt : v.val - u.val < p := by omega
  have hcop : p.Coprime (v.val - u.val) :=
    hp.coprime_iff_not_dvd.mpr fun hd => (Nat.not_dvd_of_pos_of_lt hpos hlt) hd
  have hd := Int.modEq_iff_dvd.mp (hu.trans hv.symm)
  have hd' : (m : ℤ) ∣ (((v.val - u.val) * P : ℕ) : ℤ) := by
    convert hd using 1
    rw [Nat.cast_mul, Nat.cast_sub huv'.le]
    ring
  have hnat : m ∣ (v.val - u.val) * P := Int.natCast_dvd_natCast.mp hd'
  have hboth := Nat.dvd_gcd (by simpa only [Nat.mul_comm] using hm : m ∣ p * P) hnat
  rw [Nat.gcd_mul_right, hcop.gcd_eq_one, one_mul] at hboth
  exact hn hboth

/-- Fewer than `p` new congruences leave a free extension to the next period. -/
theorem exists_uncovered_extension {p P : ℕ} (hp : p.Prime) (x : ℤ)
    (F : Finset (ℕ × ℤ)) (hcard : F.card < p)
    (hF : ∀ b ∈ F, b.1 ∣ P * p ∧ ¬ b.1 ∣ P) :
    ∃ j : Fin p, ∀ b ∈ F, ¬ (x + (j.val : ℤ) * P ≡ b.2 [ZMOD b.1]) := by
  classical
  let blocked (b : ℕ × ℤ) : Finset (Fin p) :=
    Finset.univ.filter fun j => x + (j.val : ℤ) * P ≡ b.2 [ZMOD b.1]
  have hs : (F.biUnion blocked).card ≤ F.card := by
    calc
      _ ≤ ∑ b ∈ F, (blocked b).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ F, 1 := by
        apply Finset.sum_le_sum
        intro b hb
        rcases hF b hb with ⟨hm, hn⟩
        apply Finset.card_le_one.mpr
        intro i hi j hj
        exact single_forbidden_extension hp hm hn
          (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
      _ = F.card := by simp
  have hd : (F.biUnion blocked).card < (Finset.univ : Finset (Fin p)).card := by
    simpa using hs.trans_lt hcard
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hd
  refine ⟨j, ?_⟩
  intro b hb h
  exact hj (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩)

private structure Frame where
  length : ℕ
  period : ℕ → ℕ
  radix : ℕ → ℕ
  moduli : ℕ → Finset ℕ
  start : period 0 = 1
  step : ∀ i < length, period (i + 1) = period i * radix i
  prime : ∀ i < length, (radix i).Prime
  card : ∀ i < length, (moduli i).card = radix i - 1
  isNew : ∀ i < length, ∀ m ∈ moduli i, m ∣ period (i + 1) ∧ ¬ m ∣ period i
  anchorNew : ∀ i < length, period length ∉ moduli i

namespace Frame

variable (F : Frame)

private theorem period_dvd {i j : ℕ} (hij : i ≤ j) (hj : j ≤ F.length) :
    F.period i ∣ F.period j := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact dvd_rfl
  | succ j ih =>
    by_cases hi : i = j + 1
    · subst i
      exact dvd_rfl
    · have hlt : j < F.length := by omega
      exact (ih (by omega) hlt.le).trans (F.step j hlt ▸ dvd_mul_right _ _)

private theorem period_pos (i : ℕ) (hi : i ≤ F.length) : 0 < F.period i := by
  induction i with
  | zero => simp [F.start]
  | succ i ih =>
    have hlt : i < F.length := by omega
    rw [F.step i hlt]
    exact Nat.mul_pos (ih hlt.le) (F.prime i hlt).pos

private theorem layers_disjoint {i j : ℕ} (hi : i < F.length) (hj : j < F.length)
    (hij : i ≠ j) : Disjoint (F.moduli i) (F.moduli j) := by
  rw [Finset.disjoint_left]
  intro m hmi hmj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (F.isNew j hj m hmj).2 ((F.isNew i hi m hmi).1.trans
      (F.period_dvd (show i + 1 ≤ j by omega) hj.le))
  · exact (F.isNew i hi m hmi).2 ((F.isNew j hj m hmj).1.trans
      (F.period_dvd (show j + 1 ≤ i by omega) hi.le))

private theorem avoids_all_layers (constraints : ℕ → Finset (ℕ × ℤ))
    (hcard : ∀ i < F.length, (constraints i).card < F.radix i)
    (hnew : ∀ i < F.length, ∀ b ∈ constraints i,
      b.1 ∣ F.period (i + 1) ∧ ¬ b.1 ∣ F.period i) :
    ∃ z : ℤ, ∀ i < F.length, ∀ b ∈ constraints i, ¬ z ≡ b.2 [ZMOD b.1] := by
  suffices step : ∀ t ≤ F.length,
      ∃ z : ℤ, ∀ i < t, ∀ b ∈ constraints i, ¬ z ≡ b.2 [ZMOD b.1] from step _ le_rfl
  intro t ht
  induction t with
  | zero => exact ⟨0, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  | succ t ih =>
    have hlt : t < F.length := by omega
    obtain ⟨x, hx⟩ := ih hlt.le
    obtain ⟨j, hj⟩ := exists_uncovered_extension (P := F.period t) (F.prime t hlt) x
      (constraints t) (hcard t hlt) (by simpa only [F.step t hlt] using hnew t hlt)
    refine ⟨x + (j.val : ℤ) * F.period t, ?_⟩
    intro i hi b hb hc
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
    · have hd : b.1 ∣ F.period t := (hnew i (h.trans hlt) b hb).1.trans
        (F.period_dvd (show i + 1 ≤ t by omega) hlt.le)
      have hdInt : (b.1 : ℤ) ∣ (F.period t : ℤ) := by exact_mod_cast hd
      have hsame : x ≡ x + (j.val : ℤ) * F.period t [ZMOD b.1] := by
        apply Int.modEq_iff_dvd.mpr
        simpa only [add_sub_cancel_left] using dvd_mul_of_dvd_right hdInt (j.val : ℤ)
      exact hx i h b hb (hsame.trans hc)
    · exact hj b hb hc

private def layerUnion : Finset ℕ := (Finset.range F.length).biUnion F.moduli

private def withAnchor : Finset ℕ := insert (F.period F.length) F.layerUnion

private theorem anchor_not_mem : F.period F.length ∉ F.layerUnion := by
  intro h
  obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.mp h
  exact F.anchorNew i (Finset.mem_range.mp hi) hm

private noncomputable def residue (i : ℕ) (hi : i < F.length) (m : ℕ) (hm : m ∈ F.moduli i) : ℤ :=
  (F.period i : ℤ) * (((Finset.equivFinOfCardEq (F.card i hi) ⟨m, hm⟩).val : ℤ) + 1)

private noncomputable def assignment (m : ℕ) : ℤ := by
  classical
  exact if h : ∃ i < F.length, m ∈ F.moduli i then
    F.residue h.choose h.choose_spec.1 m h.choose_spec.2 else 0

private theorem assignment_of_layer (i : ℕ) (hi : i < F.length) (m : ℕ)
    (hm : m ∈ F.moduli i) : F.assignment m = F.residue i hi m hm := by
  classical
  let h : ∃ j < F.length, m ∈ F.moduli j := ⟨i, hi, hm⟩
  unfold assignment
  rw [dif_pos h]
  have heq : h.choose = i := by
    by_contra hne
    exact Finset.disjoint_left.mp (F.layers_disjoint h.choose_spec.1 hi hne)
      h.choose_spec.2 hm
  congr

private theorem assignment_of_anchor : F.assignment (F.period F.length) = 0 := by
  classical
  unfold assignment
  exact dif_neg (fun ⟨i, hi, hm⟩ => F.anchorNew i hi hm)

private theorem covers_or_zero (z : ℤ) (t : ℕ) (ht : t ≤ F.length) :
    (∃ m ∈ F.layerUnion, z ≡ F.assignment m [ZMOD m]) ∨ z ≡ 0 [ZMOD F.period t] := by
  induction t with
  | zero => right; simp [F.start, Int.ModEq]
  | succ i ih =>
    have hi : i < F.length := by omega
    rcases ih hi.le with hcovered | hzero
    · exact Or.inl hcovered
    have hdiv : (F.period i : ℤ) ∣ z := by
      simpa only [sub_zero] using Int.modEq_iff_dvd.mp hzero.symm
    obtain ⟨q, hq⟩ := hdiv
    let r := q % (F.radix i : ℤ)
    have hr : z ≡ (F.period i : ℤ) * r [ZMOD F.period (i + 1)] := by
      rw [hq, F.step i hi, Nat.cast_mul]
      exact (Int.mod_modEq q (F.radix i : ℤ)).symm.mul_left'
    by_cases h0 : r = 0
    · right
      simpa [h0] using hr
    · have hp : 0 < (F.radix i : ℤ) := by exact_mod_cast (F.prime i hi).pos
      have hr0 : 0 ≤ r := Int.emod_nonneg q hp.ne'
      have hrp : r < (F.radix i : ℤ) := Int.emod_lt_of_pos q hp
      let j : Fin (F.radix i - 1) := ⟨(r - 1).toNat, by omega⟩
      let e := Finset.equivFinOfCardEq (F.card i hi)
      let m := e.symm j
      refine Or.inl ⟨m.val, Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, m.property⟩, ?_⟩
      rw [F.assignment_of_layer i hi m.val m.property]
      have he : e m = j := e.apply_symm_apply j
      have hj : (j.val : ℤ) + 1 = r := by dsimp [j]; omega
      have ha : F.residue i hi m.val m.property = (F.period i : ℤ) * r := by
        change (F.period i : ℤ) * (((e m).val : ℤ) + 1) = _
        rw [he, hj]
      rw [ha]
      exact hr.of_dvd (by exact_mod_cast (F.isNew i hi m.val m.property).1)

private theorem withAnchor_covers (hanchor : 1 < F.period F.length) :
    Erdos1189.IsCoveringSet F.withAnchor := by
  constructor
  · intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hanchor
    · obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.mp hm
      have hn := (F.isNew i (Finset.mem_range.mp hi) m hm).2
      have hd := (F.isNew i (Finset.mem_range.mp hi) m hm).1
      have hpos := F.period_pos (i + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))
      by_contra! h
      interval_cases m <;> simp [hpos.ne'] at hd hn
  · refine ⟨F.assignment, fun z => ?_⟩
    rcases F.covers_or_zero z F.length le_rfl with ⟨m, hm, hz⟩ | hz
    · exact ⟨m, Finset.mem_insert_of_mem hm, hz⟩
    · exact ⟨F.period F.length, Finset.mem_insert_self _ _, by rwa [F.assignment_of_anchor]⟩

private theorem new_period {i : ℕ} (hi : i < F.length) : ¬ F.period (i + 1) ∣ F.period i := by
  have hpi := F.period_pos i hi.le
  apply Nat.not_dvd_of_pos_of_lt hpi
  rw [F.step i hi]
  have hmul := Nat.mul_le_mul_left (F.period i) (F.prime i hi).two_le
  omega

/-- A missing class provides enough space to avoid the final anchor as well. -/
private theorem withAnchor_irreducible (hanchor : 1 < F.period F.length) :
    Erdos1189.IsIrreducibleCoveringSet F.withAnchor := by
  classical
  refine ⟨F.withAnchor_covers hanchor, ?_⟩
  intro N hN hcover
  obtain ⟨a, ha⟩ := hcover.2
  let raw (i : ℕ) : Finset (ℕ × ℤ) :=
    ((F.moduli i).filter (· ∈ N)).image fun m => (m, a m)
  have hraw (i : ℕ) : (raw i).card ≤ (F.moduli i).card :=
    Finset.card_image_le.trans (Finset.card_filter_le _ _)
  have hraw_new (i : ℕ) (hi : i < F.length) (b : ℕ × ℤ) (hb : b ∈ raw i) :
      b.1 ∣ F.period (i + 1) ∧ ¬ b.1 ∣ F.period i := by
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hb
    exact F.isNew i hi m (Finset.mem_filter.mp hm).1
  have hraw_mem (i m : ℕ) (hm : m ∈ F.moduli i) (hn : m ∈ N) : (m, a m) ∈ raw i :=
    Finset.mem_image.mpr ⟨m, Finset.mem_filter.mpr ⟨hm, hn⟩, rfl⟩
  have avoid (z : ℤ) (hz : ∀ i < F.length, ∀ b ∈ raw i, ¬ z ≡ b.2 [ZMOD b.1])
      (hanchorZ : ∀ _ : F.period F.length ∈ N, ¬ z ≡ a (F.period F.length) [ZMOD F.period F.length]) : False := by
    obtain ⟨m, hm, hmz⟩ := ha z
    have hmF : m ∈ F.withAnchor := hN.le hm
    rcases Finset.mem_insert.mp hmF with rfl | hmF
    · exact hanchorZ hm hmz
    · obtain ⟨i, hi, hmF⟩ := Finset.mem_biUnion.mp hmF
      exact hz i (Finset.mem_range.mp hi) (m, a m) (hraw_mem i m hmF hm) hmz
  by_cases hA : F.period F.length ∈ N
  · obtain ⟨m, hm, hmN⟩ := Finset.exists_of_ssubset hN
    have hmF : m ∈ F.layerUnion := by
      rcases Finset.mem_insert.mp hm with rfl | hmF
      · exact (hmN hA).elim
      · exact hmF
    obtain ⟨i, hi0, hmi⟩ := Finset.mem_biUnion.mp hmF
    have hi := Finset.mem_range.mp hi0
    have hlt : (raw i).card < (F.moduli i).card := by
      calc
        _ ≤ ((F.moduli i).filter (· ∈ N)).card := Finset.card_image_le
        _ < (F.moduli i).card := by
          apply Finset.card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩
          intro he
          exact hmN ((Finset.mem_filter.mp (he.symm ▸ hmi)).2)
    let extra : ℕ × ℤ := (F.period (i + 1), a (F.period F.length))
    let all (j : ℕ) := if j = i then insert extra (raw j) else raw j
    have hall_raw (j : ℕ) : raw j ⊆ all j := by
      intro b hb
      by_cases h : j = i
      · subst j
        simp [all, hb]
      · simpa only [all, if_neg h] using hb
    have hc (j : ℕ) (hj : j < F.length) : (all j).card < F.radix j := by
      by_cases h : j = i
      · subst j
        have hbound := Finset.card_insert_le extra (raw i)
        simp only [all, if_pos rfl]
        have hci := F.card i hi
        omega
      · simp only [all, if_neg h]
        have hci := F.card j hj
        have hp := (F.prime j hj).pos
        have hr := hraw j
        omega
    have hnew (j : ℕ) (hj : j < F.length) (b : ℕ × ℤ) (hb : b ∈ all j) :
        b.1 ∣ F.period (j + 1) ∧ ¬ b.1 ∣ F.period j := by
      by_cases h : j = i
      · subst j
        simp only [all, if_pos rfl, Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact ⟨dvd_rfl, F.new_period hi⟩
        · exact hraw_new i hi b hb
      · exact hraw_new j hj b (by simpa only [all, if_neg h] using hb)
    obtain ⟨z, hz⟩ := F.avoids_all_layers all hc hnew
    refine avoid z (fun j hj b hb => hz j hj b (hall_raw j hb)) (fun _ hzA => ?_)
    have he : extra ∈ all i := by simp [all]
    exact hz i hi extra he (hzA.of_dvd (by
      exact_mod_cast F.period_dvd (Nat.succ_le_of_lt hi) (le_refl F.length)))
  · have hc (j : ℕ) (hj : j < F.length) : (raw j).card < F.radix j := by
      have hci := F.card j hj
      have hp := (F.prime j hj).pos
      have hr := hraw j
      omega
    obtain ⟨z, hz⟩ := F.avoids_all_layers raw hc hraw_new
    exact avoid z hz (fun h => (hA h).elim)

end Frame

section PrimeBlocks

private def radix (x i : ℕ) : ℕ :=
  if i / x ≤ x ∧ (i / x).Prime then i / x else 2

private def period (x i : ℕ) : ℕ := ∏ j ∈ Finset.range i, radix x j

private def coreLength (x : ℕ) : ℕ := (x + 1) * x

private theorem radix_prime (x i : ℕ) : (radix x i).Prime := by
  unfold radix
  split_ifs with h
  · exact h.2
  · exact Nat.prime_two

private theorem period_positive (x i : ℕ) : 0 < period x i := by
  exact Finset.prod_pos (fun j _ => (radix_prime x j).pos)

private theorem period_step (x i : ℕ) : period x (i + 1) = period x i * radix x i :=
  Finset.prod_range_succ _ _

private theorem period_dvd_period (x : ℕ) {i j : ℕ} (h : i ≤ j) : period x i ∣ period x j :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono h)

private theorem period_strict (x : ℕ) : StrictMono (period x) := by
  apply strictMono_nat_of_lt_succ
  intro i
  rw [period_step]
  have hpos := period_positive x i
  have hbound := Nat.mul_le_mul_left (period x i) (radix_prime x i).two_le
  omega

private theorem radix_on_block {x q i : ℕ} (hx : 0 < x) (hq : q ≤ x) (hprime : q.Prime)
    (hl : q * x ≤ i) (hu : i < (q + 1) * x) : radix x i = q := by
  have hdiv : i / x = q := (Nat.div_eq_iff hx).mpr ⟨hl, by rw [Nat.add_mul] at hu; omega⟩
  simp [radix, hdiv, hq, hprime]

private theorem radix_after_core {x i : ℕ} (hx : 0 < x) (hi : coreLength x ≤ i) :
    radix x i = 2 := by
  have hdiv : x + 1 ≤ i / x := (Nat.le_div_iff_mul_le hx).mpr hi
  exact if_neg fun h => by omega

private theorem prime_pow_dvd_after_block {x q i : ℕ} (hx : 0 < x) (hq : q ≤ x)
    (hprime : q.Prime) (hi : (q + 1) * x ≤ i) : q ^ x ∣ period x i := by
  let block := Finset.Ico (q * x) ((q + 1) * x)
  have hsub : block ⊆ Finset.range i := by
    intro j hj
    have hj' := (Finset.mem_Ico.mp hj).2
    exact Finset.mem_range.mpr (hj'.trans_le hi)
  have hd := Finset.prod_dvd_prod_of_subset block (Finset.range i) (radix x) hsub
  have hconst : (∏ j ∈ block, radix x j) = q ^ x := by
    calc
      _ = ∏ _j ∈ block, q := by
        apply Finset.prod_congr rfl
        intro j hj
        exact radix_on_block hx hq hprime (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2
      _ = _ := by simp [block, Nat.add_mul]
  rwa [hconst] at hd

private theorem small_tag_dvd {x i d : ℕ} (hx : 0 < x) (hpos : 0 < d) (hlt : d < radix x i) :
    d ∣ period x i := by
  by_cases hr : i / x ≤ x ∧ (i / x).Prime
  · have hdp : d < i / x := by simpa [radix, hr] using hlt
    apply (Nat.factorization_le_iff_dvd hpos.ne' (period_positive x i).ne').mp
    intro q
    by_cases hq0 : d.factorization q = 0
    · simp [hq0]
    · have hmem : q ∈ d.primeFactors := by
        rw [← Nat.support_factorization, Finsupp.mem_support_iff]
        exact hq0
      have hq := Nat.prime_of_mem_primeFactors hmem
      have hdq := Nat.dvd_of_mem_primeFactors hmem
      have hqd := Nat.le_of_dvd hpos hdq
      have hxq : q ≤ x := by omega
      have hqi : (q + 1) * x ≤ i :=
        (Nat.le_div_iff_mul_le hx).mp (by omega)
      have hpow := prime_pow_dvd_after_block hx hxq hq hqi
      apply Nat.le_trans (show d.factorization q ≤ x from by
        have := Nat.factorization_lt q hpos.ne'
        omega)
      exact (hq.pow_dvd_iff_le_factorization (period_positive x i).ne').mp hpow
  · have hd : d = 1 := by simp [radix, hr] at hlt; omega
    simp [hd]

private def newPower (x i : ℕ) : ℕ := (radix x i) ^ ((period x i).factorization (radix x i) + 1)

private def moduli (x i : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (radix x i)).image (newPower x i * ·)

private theorem moduli_card (x i : ℕ) : (moduli x i).card = radix x i - 1 := by
  unfold moduli
  rw [Finset.card_image_of_injective]
  · exact Nat.card_Ico _ _
  · exact fun _ _ h => Nat.mul_left_cancel (pow_pos (radix_prime x i).pos _) h

private theorem moduli_new {x i m : ℕ} (hx : 0 < x) (hm : m ∈ moduli x i) :
    m ∣ period x (i + 1) ∧ ¬ m ∣ period x i := by
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
  have hd1 := (Finset.mem_Ico.mp hd).1
  have hdp := (Finset.mem_Ico.mp hd).2
  have hp := radix_prime x i
  have hP := (period_positive x i).ne'
  have hcop := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hdp)).pow_left
  refine ⟨?_, ?_⟩
  · rw [period_step]
    apply (hcop _).mul_dvd_of_dvd_of_dvd
    · apply (hp.pow_dvd_iff_le_factorization (Nat.mul_ne_zero hP hp.ne_zero)).mpr
      rw [Nat.factorization_mul hP hp.ne_zero]
      simp [newPower, hp.factorization_self]
    · exact (small_tag_dvd hx (by omega) hdp).trans (dvd_mul_right _ _)
  · intro h
    have hdiv := (dvd_mul_right (newPower x i) d).trans h
    have hle := (hp.pow_dvd_iff_le_factorization hP).mp hdiv
    exact (Nat.not_succ_le_self _) hle

private theorem anchor_absent {x length i : ℕ} (hx : 3 ≤ x) (hl : coreLength x < length)
    (hi : i < length) : period x length ∉ moduli x i := by
  intro hm
  by_cases he : i + 1 = length
  · have hafter : coreLength x ≤ i := by omega
    have hp := radix_after_core (show 0 < x by omega) hafter
    have h3 : 3 ∣ period x length := by
      rw [← pow_one 3]
      have hdvd := prime_pow_dvd_after_block (q := 3) (show 0 < x by omega) hx Nat.prime_three
        (show (3 + 1) * x ≤ length by
          dsimp [coreLength] at hl
          exact (Nat.mul_le_mul_right x (by omega)).trans hl.le)
      exact (Nat.pow_dvd_pow 3 (by omega : 1 ≤ x)).trans hdvd
    obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hm
    have ha1 : a = 1 := by
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp ha
      rw [hp] at hhi
      omega
    have hpow : 3 ∣ 2 ^ ((period x i).factorization 2 + 1) := by
      rw [← heq, newPower, hp, ha1, mul_one] at h3
      exact h3
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hpow)
  · have hdiv := (moduli_new (show 0 < x by omega) hm).1
    exact (not_le_of_gt (period_strict x (show i + 1 < length by omega)))
      (Nat.le_of_dvd (period_positive x (i + 1)) hdiv)

private def blockFrame (x length : ℕ) (hx : 3 ≤ x) (hl : coreLength x < length) : Frame where
  length := length
  period := period x
  radix := radix x
  moduli := moduli x
  start := by simp [period]
  step := fun i _ => period_step x i
  prime := fun i _ => radix_prime x i
  card := fun i _ => moduli_card x i
  isNew := fun _ _ _ hm => moduli_new (by omega) hm
  anchorNew := fun _ hi => anchor_absent hx hl hi

private def coreWeight (x : ℕ) : ℕ := ∑ i ∈ Finset.range (coreLength x), (radix x i - 1)

private theorem radix_le {x : ℕ} (hx : 3 ≤ x) (i : ℕ) : radix x i ≤ x := by
  unfold radix
  split_ifs with h
  · exact h.1
  · omega

private theorem weight_le {x : ℕ} (hx : 3 ≤ x) : coreWeight x ≤ (x + 1) ^ 3 := by
  calc
    _ ≤ ∑ _i ∈ Finset.range (coreLength x), x :=
      Finset.sum_le_sum fun i _ => (Nat.sub_le _ _).trans (radix_le hx i)
    _ = coreLength x * x := by simp
    _ ≤ (x + 1) ^ 3 := by
      dsimp [coreLength]
      nlinarith

private theorem weight_after {x : ℕ} (hx : 3 ≤ x) (t : ℕ) :
    (∑ i ∈ Finset.range (coreLength x + t), (radix x i - 1)) = coreWeight x + t := by
  induction t with
  | zero => simp [coreWeight]
  | succ t ih =>
    rw [Nat.add_succ, Finset.sum_range_succ, ih, radix_after_core (by omega) (by omega)]
    norm_num [Nat.add_assoc]

private theorem frame_card (F : Frame) : F.withAnchor.card =
    (∑ i ∈ Finset.range F.length, (F.radix i - 1)) + 1 := by
  rw [Frame.withAnchor, Finset.card_insert_of_notMem F.anchor_not_mem, Frame.layerUnion]
  rw [Finset.card_biUnion (fun _ hi _ hj hij => F.layers_disjoint
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij)]
  rw [Finset.sum_congr rfl (fun i hi => F.card i (Finset.mem_range.mp hi))]

private theorem first_layer_power {x p : ℕ} (hx : 3 ≤ x) (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpx : p ≤ x) : newPower x (p * x) = p := by
  have hRadix : radix x (p * x) = p := radix_on_block (by omega) hpx hp le_rfl
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self p) (by omega))
  have hnd : ¬ p ∣ period x (p * x) := by
    intro hdiv
    obtain ⟨i, hi, hd⟩ := (hp.prime.dvd_finsetProd_iff (radix x)).mp hdiv
    have hip : i / x < p := (Nat.div_lt_iff_lt_mul (by omega : 0 < x)).mpr (Finset.mem_range.mp hi)
    have hlt : radix x i < p := by
      unfold radix
      split_ifs <;> omega
    exact (Nat.not_dvd_of_pos_of_lt (radix_prime x i).pos hlt) hd
  simp [newPower, hRadix, Nat.factorization_eq_zero_of_not_dvd hnd]

private noncomputable def primeMass (x : ℕ) : ℝ :=
  ∑ p ∈ (Nat.primesLE x).filter (3 ≤ ·), Real.log p / p

private theorem first_layer_mass {x p : ℕ} (hx : 3 ≤ x) (hp : p.Prime)
    (hp3 : 3 ≤ p) (hpx : p ≤ x) :
    Real.log p / p ≤ ∑ m ∈ moduli x (p * x), (m : ℝ)⁻¹ := by
  have hRadix : radix x (p * x) = p := radix_on_block (by omega) hpx hp le_rfl
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self p) (by omega))
  unfold moduli
  rw [hRadix, first_layer_power hx hp hp3 hpx, Finset.sum_image (fun a _ b _ h => Nat.mul_left_cancel hp.pos h)]
  have hharm : Real.log p ≤ (harmonic (p - 1) : ℝ) := by
    simpa only [Nat.sub_add_cancel hp.pos] using log_add_one_le_harmonic (p - 1)
  calc
    _ ≤ (harmonic (p - 1) : ℝ) / p := by gcongr
    _ = ∑ a ∈ Finset.Ico 1 p, ((p * a : ℕ) : ℝ)⁻¹ := by
      have hset : Finset.Icc 1 (p - 1) = Finset.Ico 1 p := by
        ext a
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [harmonic_eq_sum_Icc, hset, Rat.cast_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro a _
      simp [Nat.cast_mul, Rat.cast_inv, div_eq_mul_inv, mul_comm]

private theorem primeMass_le_frame {x length : ℕ} (hx : 3 ≤ x) (hl : coreLength x < length) :
    primeMass x ≤ ∑ m ∈ (blockFrame x length hx hl).withAnchor, (m : ℝ)⁻¹ := by
  classical
  let F := blockFrame x length hx hl
  let P := (Nat.primesLE x).filter (3 ≤ ·)
  have hdisj : (↑(Finset.range length) : Set ℕ).PairwiseDisjoint (moduli x) := by
    intro i hi j hj hij
    exact F.layers_disjoint (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  have himage : P.image (· * x) ⊆ Finset.range length := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    have hpx := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
    exact Finset.mem_range.mpr ((Nat.mul_le_mul_right x (show p ≤ x + 1 by omega)).trans_lt hl)
  change (∑ p ∈ P, Real.log p / p) ≤ _
  calc
    _ ≤ ∑ p ∈ P, ∑ m ∈ moduli x (p * x), (m : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpd := Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1
      exact first_layer_mass hx hpd.2 (Finset.mem_filter.mp hp).2 hpd.1
    _ = ∑ i ∈ P.image (· * x), ∑ m ∈ moduli x i, (m : ℝ)⁻¹ := by
      rw [Finset.sum_image (fun a _ b _ h => Nat.mul_right_cancel (by omega : 0 < x) h)]
    _ ≤ ∑ i ∈ Finset.range length, ∑ m ∈ moduli x i, (m : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun _ _ _ => by positivity)
    _ = ∑ m ∈ F.layerUnion, (m : ℝ)⁻¹ := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ m ∈ F.withAnchor, (m : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) (fun _ _ _ => by positivity)

private theorem exists_large_mass {x k : ℕ} (hx : 3 ≤ x) (hk : (x + 1) ^ 3 + 1 < k) :
    ∃ M : Finset ℕ, Erdos1189.IsIrreducibleCoveringSet M ∧ M.card = k ∧
      primeMass x ≤ ∑ m ∈ M, (m : ℝ)⁻¹ := by
  let t := k - (coreWeight x + 1)
  let length := coreLength x + t
  have ht : 0 < t := by
    have := weight_le hx
    dsimp [t]
    omega
  have hl : coreLength x < length := by dsimp [length]; omega
  let F := blockFrame x length hx hl
  have hanchor : 1 < period x length := by
    have h0 : period x 0 = 1 := by simp [period]
    rw [← h0]
    exact period_strict x (show 0 < length from Nat.zero_le _ |>.trans_lt hl)
  refine ⟨F.withAnchor, F.withAnchor_irreducible hanchor, ?_, primeMass_le_frame hx hl⟩
  rw [frame_card]
  change ((∑ i ∈ Finset.range (coreLength x + t), (radix x i - 1)) + 1) = k
  rw [weight_after hx]
  have := weight_le hx
  dsimp [t]
  omega

private theorem eventually_theta_lower : ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 ≤ Chebyshev.theta n := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 ht
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto ht').bound
    (by norm_num : (0 : ℝ) < 1 / 32)
  have hroot := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp_tendsto ht).bound
    (by norm_num : (0 : ℝ) < 1 / 32)
  filter_upwards [hsmall, hroot, eventually_ge_atTop (2 : ℕ)] with n hsmall hnroot hn
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs] at hsmall hnroot
  rw [← Real.sqrt_eq_rpow, abs_of_nonneg (Real.sqrt_nonneg _)] at hnroot
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)] at hsmall
  have h1 := (le_abs_self (Real.log ((n : ℝ) + 1))).trans hsmall
  have h2 := (le_abs_self (Real.log (n : ℝ))).trans hnroot
  have h2' := mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg (n : ℝ))
  have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
  have hlog : (2 : ℝ) / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog' := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ (n : ℝ) by positivity)
  have htheta := Chebyshev.theta_ge n
  push_cast at htheta
  nlinarith

private theorem exists_theta_gain : ∃ Y : ℕ, 3 ≤ Y ∧ ∀ y ≥ Y,
    (y : ℝ) / 2 ≤ Chebyshev.theta (4 * (y : ℝ)) - Chebyshev.theta y := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_theta_lower
  refine ⟨max 3 N, le_max_left _ _, ?_⟩
  intro y hy
  have hny : N ≤ y := (le_max_right 3 N).trans hy
  have h4 := hN (4 * y) (by omega)
  have hu := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ (y : ℝ) by positivity)
  have h4log : Real.log 4 ≤ (3 : ℝ) / 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  have hprod := mul_le_mul_of_nonneg_right h4log (show (0 : ℝ) ≤ (y : ℝ) by positivity)
  push_cast at h4
  linarith

private theorem primeMass_nonneg (x : ℕ) : 0 ≤ primeMass x := by
  apply Finset.sum_nonneg
  intro p hp
  have hp3 := (Finset.mem_filter.mp hp).2
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))) (by positivity)

private theorem primeMass_gain {y : ℕ} (hy : 3 ≤ y)
    (hg : (y : ℝ) / 2 ≤ Chebyshev.theta (4 * (y : ℝ)) - Chebyshev.theta y) :
    primeMass y + 1 / 8 ≤ primeMass (4 * y) := by
  let P := Nat.primesLE y
  let Q := Nat.primesLE (4 * y)
  have hPQ : P ⊆ Q := by
    intro p hp
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨by omega, hprime⟩
  have hband (p : ℕ) (hp : p ∈ Q \ P) : y < p ∧ p ≤ 4 * y := by
    obtain ⟨hq, hnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hle, hprime⟩ := Nat.mem_primesLE.mp hq
    exact ⟨lt_of_not_ge fun h => hnot (Nat.mem_primesLE.mpr ⟨h, hprime⟩), hle⟩
  have htheta : (y : ℝ) / 2 ≤ ∑ p ∈ Q \ P, Real.log p := by
    have hsum := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) hPQ
    rw [← Chebyshev.theta_eq_sum_primesLE_log y, ← Chebyshev.theta_eq_sum_primesLE_log (4 * y)] at hsum
    push_cast at hsum
    linarith
  have hmass : (1 : ℝ) / 8 ≤ ∑ p ∈ Q \ P, Real.log p / p := by
    have hpos : 0 < 4 * (y : ℝ) := by positivity
    calc
      _ ≤ (∑ p ∈ Q \ P, Real.log p) / (4 * (y : ℝ)) := by
        apply (le_div_iff₀ hpos).mpr
        linarith
      _ ≤ _ := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro p hp
        rcases hband p hp with ⟨hlo, hhi⟩
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
        have hle : (p : ℝ) ≤ 4 * (y : ℝ) := by exact_mod_cast hhi
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
        gcongr
  have hs : P.filter (3 ≤ ·) ⊆ Q.filter (3 ≤ ·) := by
    intro p hp
    obtain ⟨hpP, hp3⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hPQ hpP, hp3⟩
  have hdiff : Q.filter (3 ≤ ·) \ P.filter (3 ≤ ·) = Q \ P := by
    ext p
    by_cases hp3 : 3 ≤ p
    · simp [hp3]
    · have hb : p ∉ Q \ P := fun h => hp3 (by have := (hband p h).1; omega)
      simp [hp3, hb]
  have heq := Finset.sum_sdiff (f := fun p : ℕ => Real.log p / p) hs
  rw [hdiff] at heq
  change (∑ p ∈ Q \ P, Real.log p / p) + primeMass y = primeMass (4 * y) at heq
  linarith

private theorem primeMass_ge_steps (Y n : ℕ) (hY : 3 ≤ Y)
    (hgain : ∀ y ≥ Y, (y : ℝ) / 2 ≤ Chebyshev.theta (4 * (y : ℝ)) - Chebyshev.theta y) :
    (n : ℝ) / 8 ≤ primeMass (Y * 4 ^ n) := by
  induction n with
  | zero => simpa using primeMass_nonneg Y
  | succ n ih =>
    have hle : Y ≤ Y * 4 ^ n := by
      simpa using Nat.mul_le_mul_left Y (Nat.one_le_pow n 4 (by norm_num))
    have h := primeMass_gain (hY.trans hle) (hgain _ hle)
    rw [show 4 * (Y * 4 ^ n) = Y * 4 ^ (n+1) by rw [pow_succ]; ac_rfl] at h
    push_cast
    linarith

private theorem step_count_le_max {Y k : ℕ} (hY : 3 ≤ Y)
    (hg : ∀ y ≥ Y, (y : ℝ) / 2 ≤ Chebyshev.theta (4 * (y : ℝ)) - Chebyshev.theta y)
    (hk : 4 * (Y + 1) ^ 3 ≤ k) :
    (Nat.log 64 (k / (4 * (Y + 1) ^ 3)) : ℝ) / 8 ≤ Erdos1189.maxReciprocalSum k := by
  let C := (Y + 1) ^ 3
  let D := 4 * C
  have hC : 0 < C := by positivity
  have hD : 0 < D := Nat.mul_pos (by decide) hC
  let z := k / D
  have hz : 0 < z := Nat.div_pos hk hD
  let n := Nat.log 64 z
  let x := Y * 4 ^ n
  have hx : 3 ≤ x := by
    have hmul := Nat.mul_le_mul_left Y (Nat.one_le_pow n 4 (by decide))
    exact hY.trans (by simpa [x] using hmul)
  have hpow : 64 ^ n ≤ z := Nat.pow_log_le_self _ hz.ne'
  have hx1 : x + 1 ≤ (Y + 1) * 4 ^ n := by
    dsimp [x]
    rw [Nat.add_mul, one_mul]
    have := Nat.one_le_pow n 4 (by decide)
    omega
  have hcubic : (x + 1) ^ 3 ≤ C * z := by
    calc
      _ ≤ ((Y + 1) * 4 ^ n) ^ 3 := Nat.pow_le_pow_left hx1 _
      _ = C * 64 ^ n := by
        dsimp [C]
        rw [mul_pow, ← pow_mul, Nat.mul_comm n 3, pow_mul]
        norm_num
      _ ≤ _ := Nat.mul_le_mul_left C hpow
  have hbudget : D * z ≤ k := Nat.mul_div_le k D
  have hfit : (x + 1) ^ 3 + 1 < k := by
    have hCz : 0 < C * z := Nat.mul_pos hC hz
    rw [show D * z = 4 * (C * z) by simp [D, Nat.mul_assoc]] at hbudget
    omega
  obtain ⟨M, hM, hcard, hmass⟩ := exists_large_mass hx hfit
  have hsup : ∑ m ∈ M, (m : ℝ)⁻¹ ≤ Erdos1189.maxReciprocalSum k := by
    unfold Erdos1189.maxReciprocalSum
    apply le_csSup
    · refine ⟨(harmonic k : ℝ), ?_⟩
      rintro s ⟨S, hS, hScard, rfl⟩
      rw [← hScard]
      exact reciprocal_le_harmonic S hS.1.1
    · exact ⟨M, hM, hcard, rfl⟩
  exact (primeMass_ge_steps Y n hY hg).trans (hmass.trans hsup)

private theorem log_of_size_le {D k : ℕ} (hD : 0 < D) (hk : D ≤ k) :
    Real.log (k : ℝ) ≤ Real.log (D : ℝ) +
      ((Nat.log 64 (k / D) : ℝ) + 1) * Real.log 64 := by
  let n := Nat.log 64 (k / D)
  have hdiv : k / D + 1 ≤ 64 ^ (n + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have hlt : k < D * (k / D + 1) := by
    have hmod := Nat.mod_lt k hD
    have hadd := Nat.div_add_mod k D
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hle : k ≤ D * 64 ^ (n + 1) := hlt.le.trans (Nat.mul_le_mul_left D hdiv)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hD.trans_le hk
  have hcast : (k : ℝ) ≤ (D : ℝ) * (64 : ℝ) ^ (n + 1) := by exact_mod_cast hle
  have hl := Real.log_le_log hkpos hcast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
  push_cast at hl
  exact hl

theorem maxReciprocalSum_theta_log :
    Erdos1189.maxReciprocalSum =Θ[atTop] (fun k : ℕ => Real.log (k : ℝ)) := by
  obtain ⟨Y, hY, hg⟩ := exists_theta_gain
  let D : ℕ := 4 * (Y + 1) ^ 3
  have hD : 0 < D := by positivity
  have h64 : 0 < Real.log 64 := Real.log_pos (by norm_num)
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ k : ℕ in atTop, 0 ≤ Erdos1189.maxReciprocalSum k ∧ 1 ≤ Real.log (k : ℝ) ∧
      Real.log (k : ℝ) ≤ (16 * Real.log 64) * Erdos1189.maxReciprocalSum k := by
    filter_upwards [eventually_ge_atTop D, (tendsto_atTop.mp hlog) 1,
        (tendsto_atTop.mp hlog) (2 * (Real.log D + Real.log 64))] with k hk hlog1 hlarge
    have hstep := step_count_le_max hY hg hk
    let n := Nat.log 64 (k / D)
    change (n : ℝ) / 8 ≤ Erdos1189.maxReciprocalSum k at hstep
    have hle := log_of_size_le hD hk
    change Real.log (k : ℝ) ≤ Real.log D + ((n : ℝ) + 1) * Real.log 64 at hle
    have hn : 0 ≤ (n : ℝ) / 8 := by positivity
    refine ⟨hn.trans hstep, hlog1, ?_⟩
    have hscale := mul_le_mul_of_nonneg_left hstep (show 0 ≤ 16 * Real.log 64 by positivity)
    linarith
  constructor
  · apply IsBigO.of_bound 2
    filter_upwards [hevent] with k hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk.1, abs_of_nonneg (by linarith [hk.2.1])]
    linarith [maxReciprocalSum_le_log k, hk.2.1]
  · apply IsBigO.of_bound (16 * Real.log 64)
    filter_upwards [hevent] with k hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith [hk.2.1]), abs_of_nonneg hk.1]
    exact hk.2.2

end PrimeBlocks

end OMA.Erdos1189Reciprocal

noncomputable def OMA.answer : ℕ → ℝ := fun k => Real.log (k : ℝ)

theorem OMA.solution : Erdos1189.erdos_1189.parts.iii.answer = OMA.answer →
    type_of% @Erdos1189.erdos_1189.parts.iii := by
  intro h
  rw [h]
  exact OMA.Erdos1189Reciprocal.maxReciprocalSum_theta_log
