import OMAReductions.R_OeisA7406_conjecture_R1
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

import Mathlib.Data.Nat.Squarefree

/-!
# Prime-wise bounds for the composite A007406 conjecture

Credit: The endpoint and valuation arguments adapt @marcusbuffett's merged
OeisA7406.conjecture.R2 and the factorial numerator recurrence used there.
The simultaneous certificate checks one active squarefree product at each
prefix. The last-digit rule extends the endpoint argument to all digits.
-/

namespace OMA.A7406Finite
open Finset

set_option maxRecDepth 6000 in
private theorem local_data {p : ℕ} [Fact p.Prime] :
    (3 < p → ∀ t : ℕ, 0 < t → (p ∣ OeisA7406.a ((t+1)*p-1) ↔ p^3 ∣ OeisA7406.a t)) ∧
    (p ≤ 3 → ∀ t : ℕ, 0 < t → ¬ p ∣ OeisA7406.a t) ∧
    (p = 7 → ∀ t : ℕ, 0 < t → ¬ p^3 ∣ OeisA7406.a t) ∧
    (∀ t : ℕ, p ≤ t → p^2 ∣ OeisA7406.a t → p^2 ∣ OeisA7406.a (t/p)) ∧
    (3 < p → ∀ t r : ℕ, 0 < t → r < p → p ∣ OeisA7406.a r →
      p^3 ∣ OeisA7406.a (t*p+r) → p^3 ∣ OeisA7406.a t) := by
  let h (n : ℕ) : ℚ := ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ)^2

  have h_zero : h 0 = 0 := by simp [h]

  have h_succ (n : ℕ) : h (n+1) = h n + 1 / ((n+1 : ℕ) : ℚ)^2 := by
    dsimp only [h]
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n+1),
      Finset.sum_insert (by simp), add_comm]

  have h_pos {n : ℕ} (hn : 0 < n) : 0 < h n := by
    apply Finset.sum_pos
    · intro i hi
      have : 0 < i := (mem_Icc.mp hi).1
      positivity
    · exact ⟨1, mem_Icc.mpr ⟨le_rfl, hn⟩⟩



  let Res (x : ℚ) (z : ZMod p) : Prop :=
    ¬ p ∣ x.den ∧ (x : ZMod p) = z

  have res_add {x y : ℚ} {a b : ZMod p} (hx : Res x a) (hy : Res y b) :
      Res (x+y) (a+b) := by
    refine ⟨fun hd => (Fact.out : p.Prime).dvd_mul.mp (hd.trans (Rat.add_den_dvd x y)) |>.elim hx.1 hy.1, ?_⟩
    rw [Rat.cast_add_of_ne_zero (by simpa [ZMod.natCast_eq_zero_iff] using hx.1)
      (by simpa [ZMod.natCast_eq_zero_iff] using hy.1), hx.2, hy.2]

  have res_term {i : ℕ} (hi : ¬ p ∣ i) :
      Res ((1:ℚ) / (i:ℚ)^2) (((i:ZMod p)⁻¹)^2) := by
    have hip : (i : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hi
    have hi0 : i ≠ 0 := by rintro rfl; simp at hi
    have eq : (1:ℚ) / (i:ℚ)^2 = ((i^2:ℕ):ℚ)⁻¹ := by push_cast; rw [one_div]
    rw [eq]
    refine ⟨?_, ?_⟩
    · rw [Rat.den_inv_of_ne_zero (by positivity)]
      simpa using (show ¬ p ∣ i^2 from fun d => hi ((Fact.out : p.Prime).dvd_of_dvd_pow d))
    · rw [Rat.cast_inv_of_ne_zero (q := ((i^2:ℕ):ℚ)) (by simpa using pow_ne_zero 2 hip)]
      simp [inv_pow]

  let rem (n : ℕ) : ℚ := h n - h (n/p) / (p:ℚ)^2

  have rem_res (n : ℕ) : Res (rem n)
      (∑ i ∈ range (n+1), ((i:ZMod p)⁻¹)^2) := by
    induction n with
    | zero =>
      simp [rem, h_zero, Res, (Fact.out : p.Prime).not_dvd_one]
    | succ n ih =>
      rw [sum_range_succ]
      by_cases hd : p ∣ n+1
      · have he : rem (n+1) = rem n := by
          have hq := Nat.succ_div_of_dvd hd
          have hn : (n+1:ℕ) = p * (n/p+1) := by
            rw [← hq, Nat.mul_div_cancel' hd]
          have cast : ((n+1:ℕ):ℚ) = (p:ℚ)*((n/p:ℕ)+1:ℚ) := by exact_mod_cast hn
          dsimp only [rem]
          rw [ hq, h_succ, h_succ]
          push_cast at cast ⊢
          rw [cast, mul_pow, one_div, mul_inv_rev]
          ring
        rw [he, (ZMod.natCast_eq_zero_iff ..).mpr hd]
        simpa using ih
      · have he : rem (n+1) = rem n + 1 / ((n+1:ℕ):ℚ)^2 := by
          dsimp only [rem]
          rw [ Nat.succ_div_of_not_dvd hd, h_succ]
          ring
        rw [he]
        exact res_add ih (res_term hd)

  have block_zero (hp : 3 < p) (q : ℕ) :
      ∑ i ∈ range (q*p), ((i:ZMod p)⁻¹)^2 = 0 := by
    have z : ∑ i ∈ range p, ((i:ZMod p)⁻¹)^2 = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      have eqf (i : Fin p) : (ZMod.finEquiv p i : ZMod p) = (i.val : ZMod p) := by
        cases p with
        | zero => omega
        | succ p => exact (Fin.cast_val_eq_self _).symm
      simp_rw [← eqf]
      calc
        _ = ∑ v : ZMod p, v⁻¹^2 := Equiv.sum_comp (ZMod.finEquiv p).toEquiv _
        _ = ∑ v : ZMod p, v^2 := Equiv.sum_comp (Equiv.inv (ZMod p)) (fun v => v^2)
        _ = 0 := FiniteField.sum_pow_lt_card_sub_one _ _ (by rw [ZMod.card]; omega)
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
      simpa using z

  have val_num_iff {x : ℚ} (hx : x ≠ 0) {e : ℕ} (he : 0 < e) :
      p^e ∣ x.num.natAbs ↔ (e:ℤ) ≤ padicValRat p x := by
    have hp : p.Prime := Fact.out
    have hnum : x.num.natAbs ≠ 0 := by simpa using (Rat.num_ne_zero.mpr hx)
    rw [Nat.pow_dvd_iff_le_padicValNat hp.ne_one hnum, padicValRat_def, padicValInt]
    by_cases hden : p ∣ x.den
    · have hu : ¬ p ∣ x.num.natAbs := fun d => hp.not_dvd_one
        ((Nat.dvd_gcd d hden).trans (by simp [x.reduced.gcd_eq_one]))
      rw [padicValNat.eq_zero_of_not_dvd hu]
      omega
    · rw [padicValNat.eq_zero_of_not_dvd hden]
      omega

  have nonneg_of_res {x : ℚ} {a : ZMod p} (hx : Res x a) :
      0 ≤ padicValRat p x := by
    rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hx.1]
    simp

  have positive_of_res_zero {x : ℚ} (hx : x ≠ 0) (hz : Res x 0) :
      0 < padicValRat p x := by
    have hd : (x.den : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr hz.1
    have hn := hz.2
    rw [Rat.cast_def, div_eq_zero_iff] at hn
    have hv := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (hn.resolve_right hd)
    have hV : p^1 ∣ x.num.natAbs := by simpa [← Int.natCast_dvd] using hv
    have := (val_num_iff hx (by decide : 0 < 1)).mp hV
    omega

  have val_scale {t : ℕ} (ht : 0 < t) :
      padicValRat p (h t / (p:ℚ)^2) = padicValRat p (h t) - 2 := by
    have hp : p.Prime := Fact.out
    have hpr : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [padicValRat.div (h_pos ht).ne' (pow_ne_zero _ hpr),padicValRat.pow,
      padicValRat.self hp.one_lt]
    norm_num

  have val_split {n : ℕ} (hn : 0 < n) (ht : 0 < n/p)
      (hs : padicValRat p (h (n/p))-2 < padicValRat p (rem n) ∨ rem n = 0) :
      padicValRat p (h n) = padicValRat p (h (n/p))-2 := by
    have eq : h n = h (n/p)/(p:ℚ)^2 + rem n := by unfold rem; ring
    by_cases hz : rem n = 0
    · rw [eq, hz, add_zero, val_scale ht]
    have hp : p.Prime := Fact.out
    have hpr : (p:ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [eq, padicValRat.add_eq_of_lt (eq ▸ (h_pos hn).ne')
      (div_ne_zero (h_pos ht).ne' (pow_ne_zero _ hpr)) hz
      (by rw [val_scale ht]; exact hs.resolve_right hz), val_scale ht]

  have drop_two {n : ℕ} (ht : 0 < n/p) (hv : padicValRat p (h (n/p)) < 2) :
      padicValRat p (h n) = padicValRat p (h (n/p))-2 := by
    have hn : 0 < n := by contrapose! ht; simp [Nat.eq_zero_of_le_zero ht]
    have hi := nonneg_of_res (rem_res n)
    exact val_split hn ht (Or.inl (by omega))

  have full_res (hp : 3 < p) {q : ℕ} (hq : 0 < q) : Res (rem (q*p-1)) 0 := by
    have hpp : p.Prime := Fact.out
    have hn := Nat.mul_pos hq hpp.pos
    have R := rem_res (q*p-1)
    rw [show q*p-1+1=q*p by omega, block_zero hp q] at R
    exact R

  have prime_cube_iff (hp : 3 < p) {t : ℕ} (ht : 0 < t) :
      p ∣ OeisA7406.a ((t+1)*p-1) ↔ p^3 ∣ OeisA7406.a t := by
    let n := (t+1)*p-1
    have hn : 0 < n := by dsimp [n]; nlinarith [Nat.sub_add_cancel (by nlinarith : 1 ≤ (t+1)*p)]
    have hq : n/p = t := by
      have he : n = t*p+(p-1) := by dsimp [n]; rw [Nat.add_mul,one_mul]; omega
      rw [he,Nat.mul_comm t p,Nat.mul_add_div (by omega : 0 < p), Nat.div_eq_of_lt (by omega : p-1 < p),add_zero]
    have hr := full_res hp (q:=t+1) (by omega)
    change Res (rem n) 0 at hr
    have hnum (j : ℕ) (hj : 0 < j) (e : ℕ) (he : 0 < e) :
        p^e ∣ OeisA7406.a j ↔ (e:ℤ) ≤ padicValRat p (h j) :=
      val_num_iff (h_pos hj).ne' he
    change p ∣ OeisA7406.a n ↔ _
    rw [← pow_one p, hnum n hn 1 (by decide), pow_one, hnum t ht 3 (by decide)]
    push_cast
    have hqt : 0 < n/p := hq ▸ ht
    by_cases hz : rem n = 0
    · rw [val_split hn hqt (Or.inr hz),hq]; omega
    have hv := positive_of_res_zero hz hr
    by_cases large : 3 ≤ padicValRat p (h t)
    · simp only [large, iff_true]
      have eq : h n = h t/(p:ℚ)^2 + rem n := by unfold rem; rw [hq]; ring
      have low := padicValRat.min_le_padicValRat_add (p:=p) (eq ▸ (h_pos hn).ne')
      rw [val_scale ht] at low
      rw [eq]
      exact le_trans (le_min (by omega) (by omega)) low
    · rw [val_split hn hqt (Or.inl (by rw [hq]; omega)), hq]
      omega
  have seven_table : ∀ n : Fin 49, 0 < n.val →
      padicValRat 7 (h n.val) ≤ if n.val < 7 then 2 else 1 := by
    decide +kernel

  have seven_bound (eq7 : p = 7) (n : ℕ) (hn : 0 < n) :
      padicValRat 7 (h n) ≤ if n < 7 then 2 else 1 := by
    subst p
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hs : n < 49
      · exact seven_table ⟨n,hs⟩ hn
      have h7 := ih (n/7) (by omega) (by omega)
      rw [if_neg (by omega)] at h7 ⊢
      rw [drop_two (by omega : 0 < n/7) (by omega)]
      omega
  have tiny (hp : p ≤ 3) (t : ℕ) (ht : 0 < t) : padicValRat p (h t) ≤ 0 := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      have pp : p.Prime := Fact.out
      by_cases htp : t < p
      · interval_cases p <;> interval_cases t <;> decide +kernel
      · have hq := Nat.div_pos (by omega : p ≤ t) pp.pos
        have hv := ih (t/p) (Nat.div_lt_self ht pp.one_lt) hq
        rw [drop_two hq (by omega)]
        omega
  refine ⟨fun hp t ht => prime_cube_iff hp ht, ?_, ?_, ?_, ?_⟩
  · intro hp t ht d
    have hv := (val_num_iff (h_pos ht).ne' (e:=1) (by decide)).mp (by simpa [OeisA7406.a, h] using d)
    have hh := tiny hp t ht
    omega
  · intro h7 t ht d
    have hv := (val_num_iff (h_pos ht).ne' (e:=3) (by decide)).mp d
    have hh := seven_bound h7 t ht
    rw [h7] at hv
    split at hh <;> omega
  · intro t hpt square
    have hp : p.Prime := Fact.out
    have ht : 0 < t := hp.pos.trans_le hpt
    have hq := Nat.div_pos hpt hp.pos
    have hv := (val_num_iff (h_pos ht).ne' (e:=2) (by decide)).mp square
    apply (val_num_iff (h_pos hq).ne' (e:=2) (by decide)).mpr
    by_contra! low
    have eq := drop_two hq low
    omega
  · intro hp3 t r ht hr d cube
    let n := t*p+r
    have hp : p.Prime := Fact.out
    have hn : 0 < n := Nat.add_pos_left (Nat.mul_pos ht hp.pos) _
    have hq : n/p = t := by
      dsimp only [n]
      rw [Nat.mul_comm t p, Nat.mul_add_div hp.pos, Nat.div_eq_of_lt hr, add_zero]
    have hqt : 0 < n/p := hq.symm ▸ ht
    have hv := (val_num_iff (h_pos hn).ne' (e:=3) (by decide)).mp cube
    apply (val_num_iff (h_pos ht).ne' (e:=3) (by decide)).mpr
    by_contra! low
    have short := rem_res r
    have hcast : (h r : ZMod p) = 0 := by
      have hd : (p : ℤ) ∣ (h r).num :=
        Int.natAbs_dvd_natAbs.mp (by simpa [OeisA7406.a, h] using d)
      rw [Rat.cast_def, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd, zero_div]
    have hzero : (∑ i ∈ range (r+1), ((i:ZMod p)⁻¹)^2) = 0 := by
      have hh := short.2
      dsimp only [rem] at hh
      rw [Nat.div_eq_of_lt hr, h_zero, zero_div, sub_zero, hcast] at hh
      exact hh.symm
    have hres : Res (rem n) 0 := by
      have hh := rem_res n
      have he : n+1 = t*p+(r+1) := by simp [n, Nat.add_assoc]
      rw [he, sum_range_add, block_zero hp3 t, zero_add] at hh
      have hs : Res (rem n) (∑ i ∈ range (r+1), ((i:ZMod p)⁻¹)^2) := by
        simpa using hh
      rwa [hzero] at hs
    have hs : padicValRat p (h (n/p))-2 < padicValRat p (rem n) ∨ rem n = 0 := by
      by_cases hz : rem n = 0
      · exact Or.inr hz
      · have hx := positive_of_res_zero hz hres
        rw [hq]
        exact Or.inl (by omega)
    rw [val_split hn hqt hs, hq] at hv
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem firstDigits {p t : ℕ} (hp : p.Prime) (hpB : p ≤ 10000)
    (hp7 : p ≠ 7) (ht : 0 < t) (htp : t < p) :
    ¬ p^2 ∣ OeisA7406.a t := by
  have htBound : t ≤ 10000-1 := by omega
  let h (n : ℕ) : ℚ := ∑ k ∈ Icc 1 n, (1 : ℚ) / (k : ℚ)^2
  have h_zero : h 0 = 0 := by simp [h]
  have h_succ (n : ℕ) : h (n+1) = h n + 1 / ((n+1 : ℕ) : ℚ)^2 := by
    dsimp only [h]
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega : 1 ≤ n+1),
      Finset.sum_insert (by simp), add_comm]
  let denom (i : ℕ) : ℕ := i.factorial^2
  let num : ℕ → ℕ := Nat.rec 0 (fun i last => last*(i+1)^2 + denom i)
  have denom_succ (i : ℕ) : denom (i+1) = denom i*(i+1)^2 := by
    simp [denom, Nat.factorial_succ, mul_pow, mul_comm]
  have h_fraction (i : ℕ) : h i = (Nat.cast (num i) : ℚ)/(Nat.cast (denom i) : ℚ) := by
    induction i with
    | zero => simp [num, h_zero]
    | succ i ih =>
      have hd : (Nat.cast (denom i) : ℚ) ≠ 0 := by dsimp [denom]; positivity
      rw [h_succ, ih, show num (i+1) = num i*(i+1)^2 + denom i by rfl, denom_succ]
      push_cast
      field_simp
  have num_dvd (i : ℕ) : OeisA7406.a i ∣ num i := by
    have hd : (Nat.cast (denom i) : ℤ) ≠ 0 := by dsimp [denom]; positivity
    have eq : h i = Rat.divInt (Nat.cast (num i) : ℤ) (Nat.cast (denom i) : ℤ) := by
      rw [h_fraction, Rat.divInt_eq_div]; push_cast; rfl
    have hv := Rat.num_dvd (Nat.cast (num i) : ℤ) hd
    rw [← eq] at hv
    change (h i).num.natAbs ∣ num i
    simpa using (Int.natAbs_dvd_natAbs.mpr hv)
  -- At stage i the product contains all primes at most i, each once.
  let selected (i q : ℕ) : Bool := decide (2 ≤ i) && (Nat.gcd i q == 1)
  let Q : ℕ → ℕ := Nat.rec 1 (fun i q => if selected (i+1) q then q * (i+1) else q)
  have Qprops (B : ℕ) : Squarefree (Q B) ∧
      ∀ s : ℕ, s.Prime → (s ∣ Q B ↔ s ≤ B) := by
    induction B with
    | zero =>
      refine ⟨squarefree_one, fun s hs => ?_⟩
      simp [Q, hs.not_dvd_one, hs.ne_zero]
    | succ B ih =>
      have hnext : Q (B+1) =
          (if selected (B+1) (Q B) then Q B * (B+1) else Q B) := rfl
      have htest : 2 ≤ B+1 ∧ Nat.gcd (B+1) (Q B) = 1 ↔ (B+1).Prime := by
        constructor
        · rintro ⟨hge,hco⟩
          by_contra bad
          obtain ⟨q,hq,hqd⟩ := Nat.exists_prime_and_dvd (by omega : B+1 ≠ 1)
          have hne : q ≠ B+1 := fun h => bad (h ▸ hq)
          have hle := Nat.le_of_dvd (by omega : 0 < B+1) hqd
          have d := Nat.dvd_gcd hqd ((ih.2 q hq).mpr (by omega))
          rw [hco] at d
          exact hq.not_dvd_one d
        · intro hb
          exact ⟨hb.two_le, hb.coprime_iff_not_dvd.mpr (fun d => by
            have hle := (ih.2 _ hb).mp d
            omega)⟩
      have hselected : selected (B+1) (Q B) = true ↔ 2 ≤ B+1 ∧ Nat.gcd (B+1) (Q B) = 1 := by
        simp [selected]
      rw [hnext]
      split_ifs with hB
      · have test := hselected.mp hB
        have hb := htest.mp test
        refine ⟨?_, ?_⟩
        · rw [squarefree_mul_iff, ← Nat.coprime_iff_isRelPrime]
          exact ⟨(show (B+1).Coprime (Q B) from test.2).symm, ih.1, hb.squarefree⟩
        · intro s hs
          rw [hs.dvd_mul, ih.2 s hs, Nat.prime_dvd_prime_iff_eq hs hb]
          omega
      · refine ⟨ih.1, fun s hs => ?_⟩
        rw [ih.2 s hs]
        by_contra! bad
        have hse : s = B+1 := by omega
        exact hB (hselected.mpr (htest.mpr (hse ▸ hs)))
  let product := Q 10000
  let exclusions := Nat.gcd product 7
  let seed := product/exclusions
  have hseed : seed*exclusions = product := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have seed_dvd : seed ∣ product := ⟨exclusions, hseed.symm⟩
  have seed_sf : Squarefree seed := (Qprops 10000).1.squarefree_of_dvd seed_dvd
  have p_seed : p ∣ seed := by
    have hd : p ∣ product := (Qprops 10000).2 p hp |>.mpr hpB
    rw [← hseed] at hd
    refine (hp.dvd_mul.mp hd).resolve_right (fun h => ?_)
    exact hp7 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp
      (h.trans (Nat.gcd_dvd_right product 7)))
  -- For a squarefree q, gcd(w, gcd(w,q)^2) = gcd(w,q) excludes square divisors from q.
  -- Remove primes once their values are reached, so the scan only checks first digits.
  let scan (k : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool := Nat.rec
    (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool)
    (fun _ _ _ _ => true)
    (fun _ next i q u v =>
      let s := (i+1)^2
      let q' := q / Nat.gcd q (i+1)
      let M := q'^2
      let w := (u*s+v)%M
      let g := Nat.gcd w q'
      Nat.gcd w (g*g) == g && next (i+1) q' w (v*s%M)) k
  have scan_sound (k i q u v : ℕ) (hsq : Squarefree q)
      (hu : u ≡ num i [MOD q^2]) (hv : v ≡ denom i [MOD q^2])
      (ok : scan k i q u v = true) :
      ∀ p t : ℕ, p.Prime → p ∣ q → i < t → t ≤ i+k → t < p → ¬ p^2 ∣ num t := by
    induction k generalizing i q u v with
    | zero => omega
    | succ k ih =>
      let q' := q / Nat.gcd q (i+1)
      let M := q'^2
      let w := (u*(i+1)^2+v)%M
      let g := Nat.gcd w q'
      change (Nat.gcd w (g*g) == g && scan k (i+1) q' w (v*(i+1)^2 % M)) = true at ok
      simp only [Bool.and_eq_true, beq_iff_eq] at ok
      have hq : q' * Nat.gcd q (i+1) = q := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
      have hq' : q' ∣ q := ⟨_, hq.symm⟩
      have hM : M ∣ q^2 := pow_dvd_pow_of_dvd hq' 2
      have hws : w ≡ num (i+1) [MOD M] :=
        (Nat.mod_modEq _ _).trans (((hu.of_dvd hM).mul_right _).add (hv.of_dvd hM))
      have hvs : v*(i+1)^2 % M ≡ denom (i+1) [MOD M] := by
        rw [denom_succ]
        exact (Nat.mod_modEq _ _).trans ((hv.of_dvd hM).mul_right _)
      intro p t hp hpq hit htk htp
      have hqp : p ∣ q' := by
        have hh : p ∣ q' * Nat.gcd q (i+1) := by rwa [hq]
        exact (hp.dvd_mul.mp hh).resolve_right (fun hd =>
          (Nat.not_dvd_of_pos_of_lt (by omega) (by omega : i+1 < p))
            (hd.trans (Nat.gcd_dvd_right _ _)))
      rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hit) with rfl | hlt
      · intro d
        have hd := (hws.dvd_iff (pow_dvd_pow_of_dvd hqp 2)).mpr d
        have hpg : p ∣ g := Nat.dvd_gcd ((dvd_pow_self _ (by decide : 2 ≠ 0)).trans hd) hqp
        have hg : p*p ∣ g := by
          rw [← ok.1]
          exact Nat.dvd_gcd (by simpa [pow_two] using hd) (Nat.mul_dvd_mul hpg hpg)
        exact Nat.squarefree_iff_prime_squarefree.mp hsq p hp
          (hg.trans ((Nat.gcd_dvd_right _ _).trans hq'))
      · exact ih (i+1) q' w (v*(i+1)^2 % M) (hsq.squarefree_of_dvd hq') hws hvs ok.2
          p t hp hqp hlt (by omega) htp
  have certificate : scan (10000-1) 0 seed 0 1 = true := by
    decide +kernel
  have hu0 : 0 ≡ num 0 [MOD seed^2] := Nat.ModEq.refl 0
  have hv0 : 1 ≡ denom 0 [MOD seed^2] := Nat.ModEq.refl 1
  have valid := scan_sound (10000-1) 0 seed 0 1 seed_sf hu0 hv0
  have bound := valid certificate p t hp p_seed ht htBound htp
  exact fun hd => bound (hd.trans (num_dvd t))

private theorem boundedNoCube {p : ℕ} [Fact p.Prime] (hb : p ≤ 10000)
    (t : ℕ) (ht : 0 < t) : ¬ p^3 ∣ OeisA7406.a t := by
  have hp : p.Prime := Fact.out
  obtain ⟨_, _, seven, parent, _⟩ := local_data (p := p)
  by_cases h7 : p = 7
  · exact seven h7 t ht
  have noSquare (i : ℕ) (hi : 0 < i) : ¬ p^2 ∣ OeisA7406.a i := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      by_cases hs : i < p
      · exact firstDigits hp hb h7 hi hs
      · intro d
        have hpi : p ≤ i := by omega
        exact ih (i/p) (Nat.div_lt_self hi hp.one_lt) (Nat.div_pos hpi hp.pos) (parent i hpi d)
  exact fun d => noSquare t ht ((pow_dvd_pow p (by decide : 2 ≤ 3)).trans d)

end OMA.A7406Finite

namespace OMA.R_OeisA7406_conjecture_R1_H2_R2

/-- Exclude prime cubes at positive single-digit prefixes for primes outside the certified range. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → 10000 < p → ∀ t : ℕ, 0 < t → t < p → ¬ p^3 ∣ OeisA7406.a t

/-- Exclude a first cube at a child of a square-divisible prefix with nonzero last-digit residue. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → 10000 < p → ∀ t : ℕ, 0 < t →
    p^2 ∣ OeisA7406.a t → ¬ p^3 ∣ OeisA7406.a t →
    ∀ r : ℕ, r < p → ¬ p ∣ OeisA7406.a r → ¬ p^3 ∣ OeisA7406.a (t*p+r)

open OMA.A7406Finite

theorem main : H1 → H2 → OMA.R_OeisA7406_conjecture_R1.H2 := by
  intro roots children n hn comp
  rw [OeisA89026.a, if_neg comp]
  apply Nat.coprime_iff_gcd_eq_one.mp
  apply Nat.coprime_of_dvd
  intro p hp hpn hpa
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨endpoint, tiny, _, parent, lastDigit⟩ := local_data (p := p)
  by_cases small : p ≤ 3
  · exact tiny small (n-1) (by omega) hpa
  obtain ⟨q, eq⟩ := hpn
  have hq : 1 < q := by
    by_contra! bad
    interval_cases q <;> simp_all
  have rep : n = ((q-1)+1)*p := by
    rw [Nat.sub_add_cancel (by omega), Nat.mul_comm]
    exact eq
  rw [rep] at hpa
  have cube := (endpoint (by omega) (q-1) (by omega)).mp hpa
  by_cases hb : p ≤ 10000
  · exact boundedNoCube hb (q-1) (by omega) cube
  have noCube (t : ℕ) (ht : 0 < t) : ¬ p^3 ∣ OeisA7406.a t := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      by_cases digit : t < p
      · exact roots p hp (by omega) t ht digit
      · intro d
        have ht' : p ≤ t := by omega
        have hqpos := Nat.div_pos ht' hp.pos
        have hqLt := Nat.div_lt_self ht hp.one_lt
        have hr := Nat.mod_lt t hp.pos
        have parNoCube := ih (t/p) hqLt hqpos
        have parSquare := parent t ht' ((pow_dvd_pow p (by decide : 2 ≤ 3)).trans d)
        have childCube : p^3 ∣ OeisA7406.a ((t/p)*p+t%p) := by
          rwa [Nat.div_add_mod' t p]
        by_cases hzero : p ∣ OeisA7406.a (t%p)
        · exact parNoCube (lastDigit (by omega) (t/p) (t%p) hqpos hr hzero childCube)
        · exact children p hp (by omega) (t/p) hqpos parSquare parNoCube (t%p) hr hzero childCube
  exact noCube (q-1) (by omega) cube

end OMA.R_OeisA7406_conjecture_R1_H2_R2
