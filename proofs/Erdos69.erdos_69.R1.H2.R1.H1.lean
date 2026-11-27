import OMAReductions.R_Erdos69_erdos_69_R1_H2_R1

/-!
# The one-point estimate for the Erdős 69 reduction

The divisor expansion reduces the mean to counting residue classes. The
number of terms is bounded by a squarefree product estimate and Chebyshev’s
prime-counting bound.
-/

-- Credit: @1tomaszmiller



namespace Erd69Divisor

open Finset

noncomputable def roughSquarefreeSupport (y : ℝ) (U : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 U).filter (fun j => Squarefree j ∧ ∀ p ∈ j.primeFactors, y < (p : ℝ))

lemma mem_roughSquarefreeSupport (y : ℝ) (U j : ℕ) :
    j ∈ roughSquarefreeSupport y U ↔
      (1 ≤ j ∧ j ≤ U) ∧ Squarefree j ∧ ∀ p ∈ j.primeFactors, y < (p : ℝ) := by
  classical
  simp only [roughSquarefreeSupport, mem_filter, mem_Icc]

lemma prime_count_transform_divisor (y δ : ℝ) (U k : ℕ) (hk : 0 < k) (hkU : k ≤ U) :
    (1 - δ) ^ (k.primeFactors.filter (fun p : ℕ => y < (p : ℝ))).card =
      ∑ j ∈ roughSquarefreeSupport y U, if j ∣ k then (-δ) ^ j.primeFactors.card else 0 := by
  classical
  let S := k.primeFactors.filter (fun p : ℕ => y < (p : ℝ))
  have hpower : (1 - δ) ^ S.card = ∑ s ∈ S.powerset, (-δ) ^ s.card := by
    simpa only [Finset.prod_const, one_pow, mul_one, neg_add_eq_sub] using
      (Finset.prod_add (fun _ : ℕ => -δ) (fun _ => (1 : ℝ)) S)
  have hsubset (s : Finset ℕ) (hs : s ∈ S.powerset) : s ⊆ k.primeFactors :=
    (mem_powerset.mp hs).trans (Finset.filter_subset _ _)
  have hprime (s : Finset ℕ) (hs : s ∈ S.powerset) :
      ∀ p ∈ s, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hsubset s hs hp)
  have hpf (s : Finset ℕ) (hs : s ∈ S.powerset) :
      (∏ p ∈ s, p).primeFactors = s := Nat.primeFactors_prod (hprime s hs)
  change (1 - δ) ^ S.card = _
  rw [hpower, ← Finset.sum_filter (s := roughSquarefreeSupport y U)
    (fun j => j ∣ k) (fun j => (-δ) ^ j.primeFactors.card)]
  refine Finset.sum_bij' (fun s _ => ∏ p ∈ s, p) (fun j _ => j.primeFactors)
    ?_ ?_ ?_ ?_ ?_
  · intro s hs
    have hdvd : (∏ p ∈ s, p) ∣ k :=
      (Finset.prod_dvd_prod_of_subset _ _ (fun p => p) (hsubset s hs)).trans k.prod_primeFactors_dvd
    have hsq : Squarefree (∏ p ∈ s, p) := by
      apply Finset.squarefree_prod_of_pairwise_isCoprime
      · intro p hp q hq hpq
        exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hprime s hs p hp)
          (hprime s hs q hq)).mpr hpq)
      · exact fun p hp => (hprime s hs p hp).squarefree
    refine mem_filter.mpr ⟨(mem_roughSquarefreeSupport y U _).mpr
      ⟨⟨Nat.pos_of_ne_zero hsq.ne_zero, (Nat.le_of_dvd hk hdvd).trans hkU⟩, hsq, ?_⟩, hdvd⟩
    rw [hpf s hs]
    exact fun p hp => (mem_filter.mp (mem_powerset.mp hs hp)).2
  · intro j hj
    obtain ⟨hj, hjk⟩ := mem_filter.mp hj
    have hrough := ((mem_roughSquarefreeSupport _ _ _).mp hj).2.2
    exact mem_powerset.mpr fun p hp =>
      mem_filter.mpr ⟨Nat.primeFactors_mono hjk hk.ne' hp, hrough p hp⟩
  · exact hpf
  · intro j hj
    exact Nat.prod_primeFactors_of_squarefree
      ((mem_roughSquarefreeSupport _ _ _).mp (mem_filter.mp hj).1).2.1
  · intro s hs
    rw [hpf s hs]

lemma sum_prime_count_transform_divisor {α : Type*} (y δ : ℝ) (U : ℕ)
    (A : Finset α) (k : α → ℕ) (hk : ∀ a ∈ A, 0 < k a) (hkU : ∀ a ∈ A, k a ≤ U) :
    (∑ a ∈ A, (1 - δ) ^ ((k a).primeFactors.filter (fun p : ℕ => y < (p : ℝ))).card) =
      ∑ j ∈ roughSquarefreeSupport y U,
        (-δ) ^ j.primeFactors.card * ((A.filter (fun a => j ∣ k a)).card : ℝ) := by
  classical
  calc
    _ = ∑ a ∈ A, ∑ j ∈ roughSquarefreeSupport y U,
        if j ∣ k a then (-δ) ^ j.primeFactors.card else 0 :=
      sum_congr rfl (fun a ha => prime_count_transform_divisor y δ U (k a) (hk a ha) (hkU a ha))
    _ = ∑ j ∈ roughSquarefreeSupport y U, ∑ a ∈ A,
        if j ∣ k a then (-δ) ^ j.primeFactors.card else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter (s := A) (fun a => j ∣ k a) (fun _ => (-δ) ^ j.primeFactors.card),
        Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma transform_weighted_error {α : Type*} (y δ : ℝ) (U : ℕ) (A : Finset α) (k : α → ℕ)
    (hk : ∀ a ∈ A, 0 < k a) (hkU : ∀ a ∈ A, k a ≤ U)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (ρ : ℕ → ℝ) (E : ℝ)
    (herr : ∀ j ∈ roughSquarefreeSupport y U,
        |((A.filter (fun a => j ∣ k a)).card : ℝ) - ρ j| ≤ E) :
    |(∑ a ∈ A, (1 - δ) ^ ((k a).primeFactors.filter (fun p : ℕ => y < (p : ℝ))).card) -
      ∑ j ∈ roughSquarefreeSupport y U, (-δ) ^ j.primeFactors.card * ρ j| ≤
      ((roughSquarefreeSupport y U).card : ℝ) * E := by
  rw [sum_prime_count_transform_divisor y δ U A k hk hkU, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _j ∈ roughSquarefreeSupport y U, E := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, abs_mul]
      have hpow : |(-δ) ^ j.primeFactors.card| ≤ 1 := by
        rw [abs_pow, abs_neg, abs_of_nonneg hδ0]
        exact pow_le_one₀ hδ0 hδ1
      simpa only [one_mul] using
        (mul_le_mul hpow (herr j hj) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

lemma transform_ap_discrepancy {α : Type*} (y δ : ℝ) (U : ℕ) (A : Finset α) (k : α → ℕ)
    (hk : ∀ a ∈ A, 0 < k a) (hkU : ∀ a ∈ A, k a ≤ U)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (E : ℝ)
    (herr : ∀ j ∈ roughSquarefreeSupport y U,
        |((A.filter (fun a => j ∣ k a)).card : ℝ) - (A.card : ℝ) / j| ≤ E) :
    |(∑ a ∈ A, (1 - δ) ^ ((k a).primeFactors.filter (fun p : ℕ => y < (p : ℝ))).card) -
      (A.card : ℝ) * (∑ j ∈ roughSquarefreeSupport y U, (-δ) ^ j.primeFactors.card / j)| ≤
      E * ((roughSquarefreeSupport y U).card : ℝ) := by
  have h := transform_weighted_error y δ U A k hk hkU hδ0 hδ1 (fun j => (A.card : ℝ) / j) E herr
  have hmain :
      (∑ j ∈ roughSquarefreeSupport y U, (-δ) ^ j.primeFactors.card * ((A.card : ℝ) / j)) =
        (A.card : ℝ) * (∑ j ∈ roughSquarefreeSupport y U, (-δ) ^ j.primeFactors.card / j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [div_eq_mul_inv]
    ring
  simpa only [hmain, mul_comm E] using h

end Erd69Divisor


namespace OMA69.AP

open Finset

/-- A residue class in an initial segment contains either the quotient or its successor. -/
lemma count_index_residue (k d c : ℕ) (hd : 0 < d) :
    |(((range k).filter fun i => i ≡ c [MOD d]).card : ℝ) - (k : ℝ) / d| ≤ 1 := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hl : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) / d := Nat.cast_div_le
  have hu : (k : ℝ) / d < ((k / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hdR).2
    exact_mod_cast (Nat.div_lt_iff_lt_mul hd).1 (Nat.lt_succ_self (k / d))
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card k hd c]
  push_cast
  have hIndicator : (0 : ℝ) ≤ (if c % d < k % d then 1 else 0) ∧
      (if c % d < k % d then 1 else 0) ≤ (1 : ℝ) := by
    split_ifs <;> norm_num
  exact abs_le.2 ⟨by linarith [hIndicator.1], by linarith [hIndicator.2]⟩

/-- Translating the interval to zero leaves the same one-point discrepancy bound. -/
lemma count_modCard (L U Q b : ℕ) (hQ : 0 < Q) :
    let I := Finset.Icc L U
    |((I.filter (fun n => n % Q = b % Q)).card : ℝ) - (I.card : ℝ) / Q| ≤ 1 := by
  intro I
  have : NeZero Q := ⟨hQ.ne'⟩
  let length := U + 1 - L
  let shift : ℕ ↪ ℕ := ⟨(L + ·), fun _ _ h => Nat.add_left_cancel h⟩
  let residue : ZMod Q := (b : ZMod Q) - (L : ZMod Q)
  have hinterval : I = (range length).map shift := by
    ext n
    simp only [I, mem_Icc, mem_map, mem_range]
    change L ≤ n ∧ n ≤ U ↔ ∃ i, i < U + 1 - L ∧ L + i = n
    constructor
    · intro hn
      exact ⟨n - L, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  have hres (i : ℕ) : (L + i) % Q = b % Q ↔ i ≡ residue.val [MOD Q] := by
    change (L + i) ≡ b [MOD Q] ↔ i ≡ residue.val [MOD Q]
    rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff,
      ZMod.natCast_zmod_val, Nat.cast_add]
    rw [add_comm (L : ZMod Q), eq_sub_iff_add_eq]
  have hfilters : (I.filter (fun n => n % Q = b % Q)) =
      ((range length).filter (fun i => i ≡ residue.val [MOD Q])).map shift := by
    rw [hinterval, filter_map]
    congr 1
    ext i
    simp only [mem_filter]
    exact and_congr_right fun _ => hres i
  rw [hfilters, card_map, hinterval, card_map, card_range]
  exact count_index_residue length Q residue.val hQ

/-- The Chinese remainder theorem turns a shifted divisibility condition into one
class modulo the product. Comparing the two interval estimates costs at most two. -/
lemma count_dvd_shift (L U Q b d : ℕ) (r : ℤ) (hQ : 0 < Q) (hd : 0 < d)
    (hc : Q.Coprime d) :
    let N := (Finset.Icc L U).filter (fun n => n % Q = b % Q)
    |((N.filter (fun n : ℕ => (d : ℤ) ∣ (n : ℤ) + r)).card : ℝ) -
      (N.card : ℝ) / d| ≤ 2 := by
  intro N
  have : NeZero d := ⟨hd.ne'⟩
  let I := Icc L U
  let s := ((-r : ℤ) : ZMod d).val
  let z := Nat.chineseRemainder hc b s
  have hs (n : ℕ) : (d : ℤ) ∣ (n : ℤ) + r ↔ n ≡ s [MOD d] := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← ZMod.natCast_eq_natCast_iff]
    simp only [Int.cast_add, Int.cast_natCast, s, ZMod.natCast_zmod_val, Int.cast_neg]
    exact eq_neg_iff_add_eq_zero.symm
  have hfilters : N.filter (fun n : ℕ => (d : ℤ) ∣ (n : ℤ) + r) =
      I.filter (fun n => n % (Q * d) = z.val % (Q * d)) := by
    ext n
    simp only [N, I, mem_filter, hs]
    change (n ∈ I ∧ n ≡ b [MOD Q]) ∧ n ≡ s [MOD d] ↔
      n ∈ I ∧ n ≡ z.val [MOD Q * d]
    rw [← Nat.modEq_and_modEq_iff_modEq_mul hc]
    constructor
    · rintro ⟨⟨hn, hnb⟩, hns⟩
      exact ⟨hn, hnb.trans z.prop.1.symm, hns.trans z.prop.2.symm⟩
    · rintro ⟨hn, hb, hd⟩
      exact ⟨⟨hn, hb.trans z.prop.1⟩, hd.trans z.prop.2⟩
  have hprod := count_modCard L U (Q * d) z.val (Nat.mul_pos hQ hd)
  have hbase := count_modCard L U Q b hQ
  change |((I.filter (fun n => n % (Q * d) = z.val % (Q * d))).card : ℝ) -
    (I.card : ℝ) / (↑(Q * d) : ℝ)| ≤ 1 at hprod
  rw [Nat.cast_mul] at hprod
  change |(N.card : ℝ) - (I.card : ℝ) / Q| ≤ 1 at hbase
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbaseScaled : |((N.card : ℝ) - (I.card : ℝ) / Q) / d| ≤ 1 := by
    rw [abs_div, abs_of_pos hdR, div_le_iff₀ hdR, one_mul]
    exact hbase.trans hdOne
  rw [sub_div, div_div] at hbaseScaled
  rw [hfilters]
  have hlo := abs_le.mp hprod
  have hhi := abs_le.mp hbaseScaled
  exact abs_le.2 ⟨by linarith [hlo.1, hhi.2], by linarith [hlo.2, hhi.1]⟩

lemma progression_card_lower (x Q b : ℕ) (hQ : 0 < Q) (hlarge : 4 * Q ≤ x) :
    (x : ℝ) / (4 * Q) ≤ (((Icc (x / 2) x).filter (fun n => n % Q = b % Q)).card : ℝ) := by
  have hQreal : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hhalf : (x : ℝ) / 2 ≤ ((Icc (x / 2) x).card : ℝ) := by
    rw [Nat.card_Icc, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
    have hdiv : ((x / 2 : ℕ) : ℝ) * 2 ≤ (x : ℝ) := by
      exact_mod_cast Nat.div_mul_le_self x 2
    linarith
  have hratio : (x : ℝ) / (2 * Q) ≤ ((Icc (x / 2) x).card : ℝ) / Q := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hhalf hQreal.le
  have hunit : (1 : ℝ) ≤ (x : ℝ) / (4 * Q) := by
    refine (le_div_iff₀ (by positivity)).2 ?_
    rw [one_mul]
    exact_mod_cast hlarge
  have hfactor : (x : ℝ) / (2 * Q) = 2 * ((x : ℝ) / (4 * Q)) := by
    field_simp
    ring
  rw [hfactor] at hratio
  have hap := (abs_le.mp (count_modCard (x / 2) x Q b hQ)).1
  linarith

end OMA69.AP


namespace OMA69.OnePoint

open Filter

lemma eventually_scale (C ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop,
      let B := Real.exp (Real.sqrt (Real.log (Real.log x)))
      0 < Real.log x ∧ 8 * B + 8 ≤ (x : ℝ) ∧
      B < (x : ℝ) ^ (1 / 200 : ℝ) ∧ 16 * C * B ≤ ε * Real.log x := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  filter_upwards [hnat.eventually_ge_atTop (256 : ℝ),
    hloglim.eventually_ge_atTop (Real.exp 4),
    hloglim.eventually_ge_atTop (40001 : ℝ),
    hloglim.eventually_ge_atTop ((16 * C / ε) ^ 2)] with x hx hlexp hlbig hlerror
  let t := Real.log (x : ℝ)
  let s := Real.log t
  let B := Real.exp (Real.sqrt s)
  change 0 < t ∧ 8 * B + 8 ≤ (x : ℝ) ∧ B < (x : ℝ) ^ (1 / 200 : ℝ) ∧
    16 * C * B ≤ ε * t
  have ht : 0 < t := by linarith
  have hx0 : 0 < (x : ℝ) := by linarith
  have hs : 4 ≤ s := (Real.le_log_iff_exp_le ht).2 hlexp
  have hs0 : 0 ≤ s := by linarith
  have ht0 : 0 ≤ t := ht.le
  have hs2 : 2 ≤ Real.sqrt s := (Real.le_sqrt (by norm_num) hs0).2 (by linarith)
  have hs_half : Real.sqrt s ≤ s / 2 := by
    have h := mul_le_mul_of_nonneg_right hs2 (Real.sqrt_nonneg s)
    rw [← pow_two, Real.sq_sqrt hs0] at h
    linarith
  have ht_sqrt : Real.exp (s / 2) = Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    congr 1
    dsimp [s]
    ring
  have hB : B ≤ Real.sqrt t := (Real.exp_le_exp.mpr hs_half).trans_eq ht_sqrt
  have htx : t ≤ x := by
    have h := Real.log_le_sub_one_of_pos hx0
    dsimp only [t]
    linarith
  have hBx := hB.trans (Real.sqrt_le_sqrt htx)
  have hx16 : 16 ≤ Real.sqrt (x : ℝ) := (Real.le_sqrt (by norm_num) hx0.le).2 (by linarith)
  have hsize : 8 * B + 8 ≤ (x : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hx16 (Real.sqrt_nonneg (x : ℝ))
    rw [← pow_two, Real.sq_sqrt hx0.le] at h
    linarith
  have hst : s ≤ t := by
    have h := Real.log_le_sub_one_of_pos ht
    dsimp only [s]
    linarith
  have h200 : 200 < Real.sqrt t := (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 200)).2 (by linarith)
  have hsmall : Real.sqrt s < t / 200 := by
    have h := mul_lt_mul_of_pos_right h200 (Real.sqrt_pos.2 ht)
    rw [← pow_two, Real.sq_sqrt ht0] at h
    linarith [Real.sqrt_le_sqrt hst]
  have hcut : B < (x : ℝ) ^ (1 / 200 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0, show Real.log (x : ℝ) * (1 / 200 : ℝ) = t / 200 by
      dsimp [t]; ring]
    exact Real.exp_lt_exp.mpr hsmall
  have hratio : 16 * C / ε ≤ Real.sqrt t :=
    (Real.le_sqrt (by positivity) ht0).2 hlerror
  have hlinear : 16 * C ≤ ε * Real.sqrt t := by
    rw [mul_comm ε]
    exact (div_le_iff₀ hε).1 hratio
  have herror : 16 * C * B ≤ ε * t := by
    calc
      16 * C * B ≤ 16 * C * Real.sqrt t := mul_le_mul_of_nonneg_left hB (by positivity)
      _ ≤ (ε * Real.sqrt t) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right hlinear (Real.sqrt_nonneg t)
      _ = ε * t := by rw [mul_assoc, ← pow_two, Real.sq_sqrt ht0]
  exact ⟨ht, hsize, hcut, herror⟩

end OMA69.OnePoint


namespace OMA69.OnePoint

open Finset Filter

/-- Legendre's formula and the trivial upper bound for a factorial. -/
lemma prime_log_sum_le (n : ℕ) (hn : 0 < n) :
    (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) ≤ 2 * Real.log n := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have hprod : (∏ p ∈ n.factorial.primeFactors,
      (p : ℝ) ^ n.factorial.factorization p) = (n.factorial : ℝ) := by
    exact_mod_cast (by simpa only [Finsupp.prod, Nat.support_factorization] using
      Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero n) :
      (∏ p ∈ n.factorial.primeFactors, p ^ n.factorial.factorization p) = n.factorial)
  have hlogprod : (∑ p ∈ n.factorial.primeFactors,
      (n.factorial.factorization p : ℝ) * Real.log p) = Real.log (n.factorial : ℝ) := by
    rw [← hprod, Real.log_prod]
    · exact sum_congr rfl fun p _ => (Real.log_pow _ _).symm
    · intro p hp
      positivity [Nat.prime_of_mem_primeFactors hp |>.pos]
  have hsubset : Nat.primesLE n ⊆ n.factorial.primeFactors := by
    intro p hp
    obtain ⟨hpn, hprime⟩ := Nat.mem_primesLE.mp hp
    exact (Nat.mem_primeFactors_of_ne_zero (Nat.factorial_ne_zero n)).2
      ⟨hprime, Nat.dvd_factorial hprime.pos hpn⟩
  apply le_of_mul_le_mul_left _ hnr
  calc
    (n : ℝ) * (∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)) =
        ∑ p ∈ Nat.primesLE n, (n : ℝ) * (Real.log p / (p : ℝ)) := mul_sum _ _ _
    _ ≤ ∑ p ∈ Nat.primesLE n, 2 * (n.factorial.factorization p : ℝ) * Real.log p := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpn, hprime⟩ := Nat.mem_primesLE.mp hp
      have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_lt.le)
      have hpr : 0 < (p : ℝ) := by exact_mod_cast hprime.pos
      have h1 : 1 ≤ n / p := (Nat.le_div_iff_mul_le hprime.pos).2 (by simpa using hpn)
      have hdiv : n ≤ (2 * (n / p)) * p := by
        have hlt : n < (n / p + 1) * p :=
          (Nat.div_lt_iff_lt_mul hprime.pos).1 (Nat.lt_succ_self _)
        exact hlt.le.trans (Nat.mul_le_mul_right _ (by omega))
      have hleg : n / p ≤ n.factorial.factorization p := by
        rw [Nat.factorization_factorial hprime (Nat.lt_succ_self (Nat.log p n))]
        have hlog1 : 1 ≤ Nat.log p n :=
          Nat.le_log_of_pow_le hprime.one_lt (by simpa using hpn)
        have hmem : 1 ∈ Ico 1 (Nat.log p n + 1) := mem_Ico.mpr ⟨le_rfl, by omega⟩
        simpa using (single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) hmem)
      have hcast : (n : ℝ) ≤ (2 * (n.factorial.factorization p : ℝ)) * (p : ℝ) := by
        exact_mod_cast hdiv.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hleg))
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hpr).2
      convert mul_le_mul_of_nonneg_right hcast hlog using 1
      ring
    _ = 2 * (∑ p ∈ Nat.primesLE n, (n.factorial.factorization p : ℝ) * Real.log p) := by
      simp only [mul_sum, mul_assoc]
    _ ≤ 2 * (∑ p ∈ n.factorial.primeFactors, (n.factorial.factorization p : ℝ) * Real.log p) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp _
      exact mul_nonneg (by positivity)
        (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le))
    _ = 2 * Real.log (n.factorial : ℝ) := by rw [hlogprod]
    _ ≤ (n : ℝ) * (2 * Real.log n) := by
      have hbound : Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ)^n) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) (by exact_mod_cast n.factorial_le_pow)
      rw [Real.log_pow] at hbound
      linarith

lemma eventually_prime_mass :
    ∀ᶠ x : ℕ in atTop, ∀ y : ℝ, (x : ℝ) ^ (1 / 200 : ℝ) ≤ y →
      (∑ p ∈ (Nat.primesLE (2*x)).filter (fun p : ℕ => y < (p : ℝ)), (1 : ℝ) / p) ≤ 800 := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with x hx y hxy
  have hx2 : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : 0 < (x : ℝ) := by linarith
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by linarith)
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hx0 _).trans_le hxy
  have hlogy : Real.log (x : ℝ) / 200 ≤ Real.log y := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hx0 (1 / 200 : ℝ)) hxy
    rw [Real.log_rpow hx0] at this
    linarith
  have hlog_2x : Real.log ((2*x : ℕ) : ℝ) ≤ 2 * Real.log (x : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) hx0.ne']
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx2]
  let P := (Nat.primesLE (2*x)).filter (fun p : ℕ => y < (p : ℝ))
  change (∑ p ∈ P, (1 : ℝ) / p) ≤ 800
  apply le_of_mul_le_mul_left _ (show 0 < Real.log (x : ℝ) / 200 by positivity)
  calc
    (Real.log (x : ℝ) / 200) * (∑ p ∈ P, (1 : ℝ) / p) =
        ∑ p ∈ P, (Real.log (x : ℝ) / 200) * ((1 : ℝ) / p) := mul_sum _ _ _
    _ ≤ ∑ p ∈ P, Real.log p / (p : ℝ) := by
      apply sum_le_sum
      intro p hp
      have hyp := (mem_filter.mp hp).2
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (hlogy.trans (Real.log_le_log hy0 hyp.le)) (by positivity)
    _ ≤ ∑ p ∈ Nat.primesLE (2*x), Real.log p / (p : ℝ) := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro p hp _
      exact div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le))
        (by positivity)
    _ ≤ 2 * Real.log ((2*x : ℕ) : ℝ) := prime_log_sum_le (2*x) (by omega)
    _ ≤ Real.log (x : ℝ) / 200 * 800 := by linarith

end OMA69.OnePoint


namespace Erd69Divisor

open Filter Finset

lemma roughSquarefree_reciprocal_le (y : ℝ) (U : ℕ) :
    (∑ m ∈ roughSquarefreeSupport y U, (1 : ℝ) / m) ≤
      Real.exp (∑ p ∈ (Nat.primesLE U).filter (fun p : ℕ => y < (p : ℝ)), (1 : ℝ) / p) := by
  classical
  let A := roughSquarefreeSupport y U
  let P := (Nat.primesLE U).filter (fun p : ℕ => y < (p : ℝ))
  have hsubset : A.image Nat.primeFactors ⊆ P.powerset := by
    intro s hs
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨⟨hm1, hmU⟩, _, hmrough⟩ := (mem_roughSquarefreeSupport y U m).mp hm
    apply Finset.mem_powerset.mpr
    intro p hp
    have hpU := (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)).trans hmU
    exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpU, Nat.prime_of_mem_primeFactors hp⟩, hmrough p hp⟩
  have hinj : Set.InjOn Nat.primeFactors (A : Set ℕ) := by
    intro m hm n hn hmn
    have hmsq := ((mem_roughSquarefreeSupport y U m).mp (Finset.mem_coe.mp hm)).2.1
    have hnsq := ((mem_roughSquarefreeSupport y U n).mp (Finset.mem_coe.mp hn)).2.1
    rw [← Nat.prod_primeFactors_of_squarefree hmsq, hmn, Nat.prod_primeFactors_of_squarefree hnsq]
  calc
    _ = ∑ s ∈ A.image Nat.primeFactors, ∏ p ∈ s, (1 : ℝ) / p := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro m hm
      have hmsq := ((mem_roughSquarefreeSupport y U m).mp hm).2.1
      simp only [one_div]
      rw [Finset.prod_inv_distrib, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hmsq]
    _ ≤ ∑ s ∈ P.powerset, ∏ p ∈ s, (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
    _ = ∏ p ∈ P, (1 + (1 : ℝ) / p) := (Finset.prod_one_add P).symm
    _ ≤ _ := Real.prod_one_add_le_exp_sum P (fun _ => by positivity)

lemma roughSquarefree_card_le_prime_splits (y : ℝ) (U : ℕ) :
    (roughSquarefreeSupport y U).card ≤ 1 + ∑ m ∈ roughSquarefreeSupport y U,
      ((Nat.primesLE (U / m)).filter (fun p : ℕ => y < (p : ℝ))).card := by
  classical
  let A := roughSquarefreeSupport y U
  let P (m : ℕ) := (Nat.primesLE (U / m)).filter (fun p : ℕ => y < (p : ℝ))
  let F (m : ℕ) := (P m).image (fun p => m * p)
  have hsub : A.erase 1 ⊆ A.biUnion F := by
    intro n hn
    have hn1 := (Finset.mem_erase.mp hn).1
    obtain ⟨⟨hnpos, hnU⟩, hnsq, hnrough⟩ :=
      (mem_roughSquarefreeSupport y U n).mp (Finset.mem_of_mem_erase hn)
    let p := n.minFac
    let m := n / p
    have hp : p.Prime := Nat.minFac_prime hn1
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hmp : m * p = n := Nat.div_mul_cancel hpn
    have hmn : m ∣ n := ⟨p, hmp.symm⟩
    have hmpos := Nat.pos_of_dvd_of_pos hmn (show 0 < n by omega)
    have hmA : m ∈ A := (mem_roughSquarefreeSupport y U m).mpr
      ⟨⟨hmpos, (Nat.le_of_dvd (by omega) hmn).trans hnU⟩,
        hnsq.squarefree_of_dvd hmn,
        fun r hr => hnrough r (Nat.primeFactors_mono hmn (by omega) hr)⟩
    have hpbound : p ≤ U / m := (Nat.le_div_iff_mul_le hmpos).mpr (by simpa [Nat.mul_comm p, hmp])
    have hpP : p ∈ P m := Finset.mem_filter.mpr
      ⟨Nat.mem_primesLE.mpr ⟨hpbound, hp⟩, hnrough p (Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩)⟩
    exact Finset.mem_biUnion.mpr ⟨m, hmA, Finset.mem_image.mpr ⟨p, hpP, hmp⟩⟩
  have hA : A.card ≤ 1 + (A.erase 1).card := by
    by_cases h : 1 ∈ A
    · have hcard := Finset.card_erase_add_one h
      omega
    · rw [Finset.erase_eq_of_notMem h]
      omega
  calc
    A.card ≤ 1 + (A.erase 1).card := hA
    _ ≤ 1 + (A.biUnion F).card := Nat.add_le_add_left (Finset.card_le_card hsub) 1
    _ ≤ 1 + ∑ m ∈ A, (F m).card := Nat.add_le_add_left Finset.card_biUnion_le 1
    _ ≤ 1 + ∑ m ∈ A, (P m).card :=
      Nat.add_le_add_left (Finset.sum_le_sum fun _ _ => Finset.card_image_le) 1

lemma roughSquarefree_count (M : ℝ)
    (hM : ∀ᶠ x : ℕ in Filter.atTop, ∀ y : ℝ, (x : ℝ) ^ (1 / 200 : ℝ) ≤ y →
      (∑ p ∈ (Nat.primesLE (2 * x)).filter (fun p : ℕ => y < (p : ℝ)), (1 : ℝ) / p) ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ y : ℝ, (x : ℝ) ^ (1 / 200 : ℝ) ≤ y →
      ((roughSquarefreeSupport y (2 * x)).card : ℝ) ≤ C * (x : ℝ) / Real.log x := by
  let K := Real.log 4 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨1 + 400 * K * Real.exp M, by positivity, ?_⟩
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  have hlim : Tendsto (fun x : ℕ => (x : ℝ) ^ (1 / 200 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 200)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hM, hlim.eventually (eventually_ge_atTop (max R 2)), eventually_ge_atTop (2 : ℕ)]
    with x hMx hxR hx2
  intro y hy
  let A := roughSquarefreeSupport y (2 * x)
  let P (m : ℕ) := (Nat.primesLE ((2 * x) / m)).filter (fun p : ℕ => y < (p : ℝ))
  have hx1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hx0 : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogx := Real.log_pos hx1
  have hP_le (m : ℕ) : ((P m).card : ℝ) ≤
      (400 * K * (x : ℝ) / Real.log x) * (1 / (m : ℝ)) := by
    by_cases hempty : P m = ∅
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      positivity
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let U := (2 * x) / m
    have hpU : p ≤ U := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1
    have hyU : y ≤ (U : ℝ) := (Finset.mem_filter.mp hp).2.le.trans (by exact_mod_cast hpU)
    have hUR : R ≤ (U : ℝ) := (le_max_left _ _).trans (hxR.trans (hy.trans hyU))
    have hU2 : (2 : ℝ) ≤ (U : ℝ) := (le_max_right _ _).trans (hxR.trans (hy.trans hyU))
    have hU0 : (0 : ℝ) < (U : ℝ) := by linarith
    have hUlog : Real.log (x : ℝ) / 200 ≤ Real.log (U : ℝ) := by
      have ht0 := Real.rpow_pos_of_pos hx0 (1 / 200 : ℝ)
      have ht := Real.log_le_log ht0 (hy.trans hyU)
      rw [Real.log_rpow hx0] at ht
      linarith
    have hcheb := hR (U : ℝ) hUR
    rw [Nat.floor_natCast] at hcheb
    calc
      ((P m).card : ℝ) ≤ ((Nat.primesLE U).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ K * (U : ℝ) / Real.log (U : ℝ) := by
        rw [Nat.primesLE_card_eq_primeCounting]
        exact hcheb
      _ ≤ K * ((2 * x) / (m : ℝ)) / (Real.log (x : ℝ) / 200) := by
        apply (div_le_div_of_nonneg_left (by positivity) (by positivity) hUlog).trans
        gcongr
        simpa [U, Nat.cast_mul] using (Nat.cast_div_le (α := ℝ) (m := 2 * x) (n := m))
      _ = (400 * K * (x : ℝ) / Real.log x) * (1 / (m : ℝ)) := by ring
  have hmain := roughSquarefree_card_le_prime_splits y (2 * x)
  have hmainR : (A.card : ℝ) ≤ 1 + ∑ m ∈ A, ((P m).card : ℝ) := by
    exact_mod_cast hmain
  have hgeom : (∑ m ∈ A, (1 : ℝ) / m) ≤ Real.exp M :=
    (roughSquarefree_reciprocal_le y (2 * x)).trans (Real.exp_le_exp.mpr (hMx y hy))
  have hone : 1 ≤ (x : ℝ) / Real.log x := by
    apply (le_div_iff₀ hlogx).mpr
    linarith [Real.log_le_sub_one_of_pos hx0]
  calc
    (A.card : ℝ) ≤ 1 + ∑ m ∈ A, ((P m).card : ℝ) := hmainR
    _ ≤ 1 + ∑ m ∈ A, (400 * K * (x : ℝ) / Real.log x) * (1 / (m : ℝ)) :=
      add_le_add (le_refl (1 : ℝ)) (Finset.sum_le_sum fun m _ => hP_le m)
    _ = 1 + (400 * K * (x : ℝ) / Real.log x) * (∑ m ∈ A, (1 : ℝ) / m) := by
      rw [Finset.mul_sum]
    _ ≤ (x : ℝ) / Real.log x + (400 * K * (x : ℝ) / Real.log x) * Real.exp M :=
      add_le_add hone (mul_le_mul_of_nonneg_left hgeom (by positivity))
    _ = (1 + 400 * K * Real.exp M) * (x : ℝ) / Real.log x := by ring

end Erd69Divisor

namespace OMA69.OnePoint

open Finset Filter Erd69Divisor

lemma cutoff_bounds {x : ℕ} {y : ℝ} (hx : 0 < Real.log (x : ℝ))
    (hy : 2 * (x : ℝ) < y ^ (101 : ℕ)) :
    (x : ℝ) ^ (1 / 200 : ℝ) ≤ y ∧ 1 < y := by
  have hx1 : (1 : ℝ) < x := (Real.log_pos_iff (Nat.cast_nonneg x)).1 hx
  have hodd : Odd (101 : ℕ) := by decide
  have hy0 : 0 < y := hodd.pow_pos_iff.mp (by linarith)
  set z := (x : ℝ) ^ (1 / 200 : ℝ) with hz
  have hz0 : 0 < z := Real.rpow_pos_of_pos (by linarith) _
  have hzp : z ^ (101 : ℕ) ≤ (x : ℝ) := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have hExp : (1 / 200 : ℝ) * ((101 : ℕ) : ℝ) ≤ 1 := by norm_num
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1.le hExp
  have hzy : z < y := by
    by_contra! hneg
    have := (pow_le_pow_left₀ hy0.le hneg 101).trans hzp
    linarith
  have hz1 : 1 ≤ z := Real.one_le_rpow hx1.le (by norm_num)
  exact ⟨hzy.le, hz1.trans_lt hzy⟩

lemma count_le_hundred (k : ℕ) (y : ℝ) (hy : 1 < y) (hk : (k : ℝ) < y ^ 101) :
    (k.primeFactors.filter fun p : ℕ => y < p).card ≤ 100 := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp
  let P := k.primeFactors.filter (fun p : ℕ => y < p)
  have hprod : (∏ p ∈ P, p) ∣ k :=
    (prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)).trans (Nat.prod_primeFactors_dvd k)
  have hle : ∏ p ∈ P, (p : ℝ) ≤ (k : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hkpos hprod
  have hpow : y ^ P.card ≤ ∏ p ∈ P, (p : ℝ) := by
    rw [← prod_const]
    exact prod_le_prod (fun _ _ => by positivity) (fun p hp => (mem_filter.mp hp).2.le)
  change P.card ≤ 100
  by_contra hc
  have hcard : 101 ≤ P.card := by omega
  exact (not_lt_of_ge ((pow_le_pow_right₀ hy.le hcard).trans (hpow.trans hle))) hk

lemma shift_natAbs_bounds {x n : ℕ} {B : ℝ} {r : ℤ} (hB : 0 ≤ B)
    (hb : 8 * B + 8 ≤ (x : ℝ)) (hr : |(r : ℝ)| ≤ B) (hn : n ∈ Icc (x / 2) x) :
    0 < ((n : ℤ) + r).natAbs ∧ ((n : ℤ) + r).natAbs ≤ 2 * x := by
  obtain ⟨hl, hu⟩ := mem_Icc.mp hn
  have hl_nat : x ≤ 2 * n + 1 := by omega
  have hlr : (x : ℝ) ≤ 2 * (n : ℝ) + 1 := by exact_mod_cast hl_nat
  have hur : (n : ℝ) ≤ x := by exact_mod_cast hu
  obtain ⟨hrl, hru⟩ := abs_le.mp hr
  have hpos_r : (0 : ℝ) < (n : ℝ) + (r : ℝ) := by linarith
  have hpos : (0 : ℤ) < (n : ℤ) + r := by exact_mod_cast hpos_r
  have hupper_r : (n : ℝ) + (r : ℝ) ≤ 2 * (x : ℝ) := by linarith
  have hupper : (n : ℤ) + r ≤ (2 * x : ℕ) := by exact_mod_cast hupper_r
  have hcast : ((((n : ℤ) + r).natAbs : ℕ) : ℤ) = (n : ℤ) + r := Int.natAbs_of_nonneg hpos.le
  constructor
  · exact Int.natAbs_pos.mpr hpos.ne'
  · exact_mod_cast hcast.trans_le hupper

lemma compare_centered_means {α : Type*} (I N : Finset α) (f g : α → ℝ)
    (m E : ℝ) (hI : 0 < I.card) (hNI : N ⊆ I) (hE : 0 ≤ E)
    (hplain : |(∑ n ∈ I, g n) - (I.card : ℝ) * m| ≤ E)
    (hshift : |(∑ n ∈ N, f n) - (N.card : ℝ) * m| ≤ E) :
    |∑ n ∈ N, (f n - (∑ a ∈ I, g a) / (I.card : ℝ))| ≤ 2 * E := by
  let μ : ℝ := (∑ a ∈ I, g a) / (I.card : ℝ)
  have hIpos : (0 : ℝ) < I.card := by exact_mod_cast hI
  have hcard : (N.card : ℝ) ≤ I.card := by exact_mod_cast card_le_card hNI
  have hmid : |m - μ| ≤ E / (I.card : ℝ) := by
    rw [abs_sub_comm, show μ - m = ((∑ a ∈ I, g a) - (I.card : ℝ) * m) / (I.card : ℝ) by
      dsimp only [μ]
      field_simp [hIpos.ne'], abs_div, abs_of_pos hIpos]
    exact div_le_div_of_nonneg_right hplain hIpos.le
  change |∑ n ∈ N, (f n - μ)| ≤ 2 * E
  rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
  calc
    _ = |((∑ n ∈ N, f n) - (N.card : ℝ) * m) + (N.card : ℝ) * (m - μ)| := by
      congr 1
      ring
    _ ≤ |(∑ n ∈ N, f n) - (N.card : ℝ) * m| + |(N.card : ℝ) * (m - μ)| := abs_add_le _ _
    _ ≤ E + (N.card : ℝ) * (E / (I.card : ℝ)) := by
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg N.card : (0 : ℝ) ≤ N.card)]
      exact add_le_add hshift (mul_le_mul_of_nonneg_left hmid (Nat.cast_nonneg _))
    _ ≤ E + (I.card : ℝ) * (E / (I.card : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hcard (div_nonneg hE hIpos.le))
    _ = 2 * E := by
      field_simp [hIpos.ne']
      ring

lemma onepoint_of_rough_bound
    (hrough : ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in atTop,
      ∀ y : ℝ, (x : ℝ) ^ (1 / 200 : ℝ) ≤ y →
        ((roughSquarefreeSupport y (2*x)).card : ℝ) ≤ C * (x : ℝ) / Real.log x) :
    OMA.R_Erdos69_erdos_69_R1_H2_R1.H1 := by
  classical
  intro δ hδ hδ1 ε hε
  obtain ⟨C, hC, hrough⟩ := hrough
  obtain ⟨X, hX⟩ := eventually_atTop.1 ((eventually_scale C ε hC hε).and hrough)
  refine ⟨X, ?_⟩
  intro x hx y hy_pow
  obtain ⟨⟨hlog, hsize, hsmall, herror⟩, hR⟩ := hX x hx
  obtain ⟨hxy, hy1⟩ := cutoff_bounds hlog hy_pow
  let B := Real.exp (Real.sqrt (Real.log (Real.log x)))
  let w : ℤ → ℕ := fun v => (v.natAbs.primeFactors.filter (fun p : ℕ => y < p)).card
  let f : ℤ → ℝ := fun v => (1 - δ) ^ w v
  let I := Icc (x / 2) x
  let μ := (∑ n ∈ I, f n) / (I.card : ℝ)
  let S := roughSquarefreeSupport y (2*x)
  let m := ∑ j ∈ S, (-δ) ^ j.primeFactors.card / (j : ℝ)
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hBR : B < y := hsmall.trans_le hxy
  have hI : 0 < I.card := card_pos.mpr ⟨x, mem_Icc.mpr ⟨Nat.div_le_self _ _, le_rfl⟩⟩
  have hIr : (0 : ℝ) < I.card := by exact_mod_cast hI
  have hshift (r : ℤ) (hr : |(r : ℝ)| ≤ B) (n : ℕ) (hn : n ∈ I) :
      0 < ((n : ℤ) + r).natAbs ∧ ((n : ℤ) + r).natAbs ≤ 2 * x :=
    shift_natAbs_bounds hB hsize hr hn
  have hmax (k : ℕ) (hk : k ≤ 2*x) : (k.primeFactors.filter fun p : ℕ => y < p).card ≤ 100 := by
    have hkreal : (k : ℝ) ≤ 2 * (x : ℝ) := by exact_mod_cast hk
    exact count_le_hundred k y hy1 (hkreal.trans_lt hy_pow)
  have hi (n : ℕ) (hn : n ∈ I) : 0 < n ∧ n ≤ 2*x := by
    simpa using hshift 0 (by simpa using hB) n hn
  have hf_lo (n : ℕ) (hn : n ∈ I) : 1 - 100 * δ ≤ f n := by
    have h := (OMA.R_Erdos69_erdos_69_R1_H2_R1.bernoulli_remainder δ hδ.le hδ1.le (w n)).1
    have hwr : (w n : ℝ) ≤ (100 : ℝ) := by
      exact_mod_cast (by simpa [w] using hmax n (hi n hn).2 : w n ≤ 100)
    have hmul := mul_le_mul_of_nonneg_left hwr hδ.le
    dsimp only [f]
    linarith
  have hf_hi (n : ℕ) : f n ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  have hμlo : 1 - 100 * δ ≤ μ := by
    apply (le_div_iff₀ hIr).2
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum hf_lo
  have hμhi : μ ≤ 1 := by
    apply (div_le_iff₀ hIr).2
    rw [one_mul, ← mul_one (I.card : ℝ), ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum (fun n _ => hf_hi n)
  have hS : (S.card : ℝ) ≤ C * (x : ℝ) / Real.log x := hR y hxy
  have hplain : |(∑ n ∈ I, f n) - (I.card : ℝ) * m| ≤ 2 * (S.card : ℝ) := by
    have h := transform_ap_discrepancy y δ (2*x) I id
      (fun n hn => (hi n hn).1) (fun n hn => (hi n hn).2) hδ.le hδ1.le 2 ?_
    · simpa only [f, w, id_eq, Int.natAbs_natCast] using h
    · intro j hj
      have hj0 : 0 < j := ((mem_roughSquarefreeSupport y (2*x) j).1 hj).1.1
      simpa only [I, Nat.mod_one, filter_true, id_eq, Int.natCast_dvd_natCast,
        Int.cast_ofNat_Int, add_zero] using
        (OMA69.AP.count_dvd_shift (x / 2) x 1 0 j 0 (by decide) hj0 (Nat.coprime_one_left j))
  refine ⟨hμlo, hμhi, ?_⟩
  intro Q b r hQ hQB hr
  let N := I.filter (fun n => n % Q = b % Q)
  have hNI : N ⊆ I := filter_subset _ _
  have h4Q : 4 * Q ≤ x := by
    have hQ4 : 4 * (Q : ℝ) ≤ (x : ℝ) := by linarith
    exact_mod_cast hQ4
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hN : (x : ℝ) / (4 * (Q : ℝ)) ≤ (N.card : ℝ) :=
    OMA69.AP.progression_card_lower x Q b hQ h4Q
  refine ⟨(fun n hn => hmax _ (hshift r hr n (hNI hn)).2), ?_⟩
  have hshifted : |(∑ n ∈ N, f ((n : ℤ) + r)) - (N.card : ℝ) * m| ≤ 2 * (S.card : ℝ) := by
    apply transform_ap_discrepancy y δ (2*x) N (fun n : ℕ => ((n : ℤ) + r).natAbs)
      (fun n hn => (hshift r hr n (hNI hn)).1) (fun n hn => (hshift r hr n (hNI hn)).2)
      hδ.le hδ1.le 2
    intro j hj
    obtain ⟨⟨hj0, _⟩, _, hjrough⟩ := (mem_roughSquarefreeSupport y (2*x) j).1 hj
    have hc : Q.Coprime j := by
      by_contra hnot
      obtain ⟨p, hp, hpQ, hpj⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
      have hpjmem : p ∈ j.primeFactors :=
        (Nat.mem_primeFactors_of_ne_zero (by omega)).2 ⟨hp, hpj⟩
      have hpQR : (p : ℝ) ≤ Q := by exact_mod_cast Nat.le_of_dvd hQ hpQ
      exact (not_lt_of_ge ((hpQR.trans hQB).trans hBR.le)) (hjrough p hpjmem)
    simpa only [I, N, Int.natCast_dvd] using
      (OMA69.AP.count_dvd_shift (x / 2) x Q b j r hQ hj0 hc)
  have hD := compare_centered_means I N (fun n => f ((n : ℤ) + r)) (fun n => f n)
    m (2 * (S.card : ℝ)) hI hNI (by positivity) hplain hshifted
  change |∑ n ∈ N, (f ((n : ℤ) + r) - μ)| ≤ ε * (N.card : ℝ)
  calc
    _ ≤ 2 * (2 * (S.card : ℝ)) := hD
    _ ≤ 4 * (C * (x : ℝ) / Real.log x) := by linarith
    _ ≤ ε * ((x : ℝ) / (4 * (Q : ℝ))) := by
      have hQerr : 16 * C * (Q : ℝ) ≤ ε * Real.log x :=
        (mul_le_mul_of_nonneg_left hQB (by positivity : 0 ≤ 16 * C)).trans herror
      have hx0 : 0 ≤ (x : ℝ) := Nat.cast_nonneg x
      have hclear := mul_le_mul_of_nonneg_right hQerr hx0
      rw [← mul_div_assoc, ← mul_div_assoc]
      apply (div_le_div_iff₀ hlog (by positivity : 0 < 4 * (Q : ℝ))).2
      convert hclear using 1 <;> ring
    _ ≤ ε * (N.card : ℝ) := mul_le_mul_of_nonneg_left hN hε.le

end OMA69.OnePoint

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R1_H2_R1.H1 :=
  OMA69.OnePoint.onepoint_of_rough_bound
    (Erd69Divisor.roughSquarefree_count 800 OMA69.OnePoint.eventually_prime_mass)
