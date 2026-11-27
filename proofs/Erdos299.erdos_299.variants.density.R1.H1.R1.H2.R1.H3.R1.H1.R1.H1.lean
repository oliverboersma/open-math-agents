import OMAReductions.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1_H1_R1

/-! Split the full prime powers of n/q at the exponential cutoff.
The product of the smaller powers has at most 2 log log N factors. -/

open Finset Real Filter

private lemma rough_split {t : ℕ} (ht : 0 < t) (Y : ℝ) (hY : 1 ≤ Y) :
    ∃ d m : ℕ, d*m = t ∧ d.Coprime m ∧
      (∀ p ∈ d.primeFactors, Y < (p : ℝ)^d.factorization p) ∧
      (m : ℝ) ≤ Y^t.primeFactors.card := by
  classical
  let P (p : ℕ) := Y < (p:ℝ)^t.factorization p
  let S := t.primeFactors.filter P
  let T := t.primeFactors.filter fun p => ¬ P p
  let f (p : ℕ) := p^t.factorization p
  let d := ∏ p ∈ S, f p
  let m := ∏ p ∈ T, f p
  have eq : d*m=t := (prod_filter_mul_prod_filter_not t.primeFactors P f).trans
    (Nat.prod_primeFactors_pow_factorization ht.ne').symm
  have hd : d ≠ 0 := fun h => ht.ne' (by simpa [h] using eq.symm)
  refine ⟨d,m,eq,?_,?_,?_⟩
  · apply Nat.coprime_prod_left_iff.mpr
    intro p hp
    apply Nat.coprime_prod_right_iff.mpr
    intro r hr
    obtain ⟨hpp,big⟩ := mem_filter.mp hp
    obtain ⟨hrr,small⟩ := mem_filter.mp hr
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hpp)
      (Nat.prime_of_mem_primeFactors hrr) (fun e => small (e ▸ big))
  · intro p hp
    have pp := Nat.prime_of_mem_primeFactors hp
    have dvd : p ∣ ∏ r ∈ S, f r := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨r,hr,hpr⟩ := (pp.prime.dvd_finsetProd_iff f).mp dvd
    have rp := Nat.prime_of_mem_primeFactors (mem_filter.mp hr).1
    have same : p = r := (Nat.prime_dvd_prime_iff_eq pp rp).mp (pp.dvd_of_dvd_pow hpr)
    subst r
    have full : f p ∣ d := dvd_prod_of_mem f hr
    have e := (pp.pow_dvd_iff_le_factorization hd).mp full
    exact (mem_filter.mp hr).2.trans_le (pow_le_pow_right₀ (by exact_mod_cast pp.one_le : (1:ℝ) ≤ p) e)
  · calc (m : ℝ) = ∏ p ∈ T, (p:ℝ)^t.factorization p := by simp [m,f]
         _ ≤ ∏ _p ∈ T, Y := prod_le_prod (fun _ _ => by positivity)
                (fun p hp => not_lt.mp (mem_filter.mp hp).2)
         _ = Y^T.card := prod_const Y
         _ ≤ _ := pow_le_pow_right₀ hY (card_le_card (filter_subset _ _))

theorem OMA.solution : OMA.R_Erdos299_erdos_299_variants_density_R1_H1_R1_H2_R1_H3_R1_H1_R1.H1 := by
  classical
  have large : ∀ᶠ N : ℕ in atTop, 0 < log (log N) :=
    ((tendsto_log_atTop.comp tendsto_log_atTop).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  filter_upwards [large,eventually_gt_atTop (1:ℕ)] with N hlarge hN
  let w := log (log N)
  let u := log N / (2*w^2)
  let M := (N:ℝ)^(1-1/w)
  have hw : 0<w := hlarge
  have Npos : (0:ℝ)<N := by exact_mod_cast (by omega : 0<N)
  have logpos : 0<log N := log_pos (by exact_mod_cast hN)
  have hu : 0<u := div_pos logpos (by positivity)
  dsimp only
  intro n q hn hnN hM count _hq dvd cop
  let t := n/q
  have qt : q*t=n := by change q*(n/q)=n; exact Nat.mul_div_cancel' dvd
  have qp : 0<q := Nat.pos_of_ne_zero fun z => hn.ne' (by simpa only [z,Nat.zero_mul] using qt.symm)
  have tp : 0<t := Nat.pos_of_ne_zero fun z => hn.ne' (by simpa only [z,Nat.mul_zero] using qt.symm)
  obtain ⟨d,m,dm,unit,rough,small⟩ := rough_split tp (exp u) (one_le_exp hu.le)
  have decomp : q*d*m=n := by rw [mul_assoc,dm,qt]
  have dp : 0<d := Nat.pos_of_ne_zero fun z => tp.ne' (by simpa only [z,Nat.zero_mul] using dm.symm)
  have divides : q*d ∣ n := ⟨m,decomp.symm⟩
  have divides' : d ∣ n := (dvd_mul_left d q).trans divides
  have qd : 0<q*d := Nat.mul_pos qp dp
  have ratio : n/(q*d)=m := by rw [←decomp,Nat.mul_div_cancel_left _ qd]
  refine ⟨d,mem_filter.mpr ⟨mem_range.mpr ((Nat.le_of_dvd hn divides').trans_lt hnN),dp,rough⟩,?_,divides,?_⟩
  · have tsub : t.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono
          (show t ∣ n by rw [← qt]; exact dvd_mul_left _ _) hn.ne'
    have count' : (t.primeFactors.card:ℝ) ≤ 2*w :=
      (show (t.primeFactors.card:ℝ) ≤ n.primeFactors.card by exact_mod_cast card_le_card tsub).trans count
    rw [← exp_nat_mul] at small
    have cap : (m:ℝ) ≤ exp (log N / w) := small.trans (exp_le_exp.mpr (calc
          (t.primeFactors.card:ℝ)*u ≤ (2*w)*u := mul_le_mul_of_nonneg_right count' hu.le
          _ = log N /w := by dsimp [u]; field_simp))
    have mass : M ≤ (q:ℝ)*d * exp (log N/w) := by
      apply hM.trans
      have nr : (n:ℝ) = (q:ℝ)*d*m := by exact_mod_cast decomp.symm
      rw [nr]
      exact mul_le_mul_of_nonneg_left cap (by positivity)
    have sep : (N:ℝ)^(-2/w) * exp (log N/w) < 1 := by
      rw [rpow_def_of_pos Npos,← exp_add,← exp_zero]
      apply exp_lt_exp.mpr
      have iden : log N * (-2/w) + log N/w = -(log N/w) := by ring
      rw [iden]
      exact neg_lt_zero.mpr (div_pos logpos hw)
    have mpos : 0<M := rpow_pos_of_pos Npos _
    apply (mul_lt_mul_iff_left₀ (exp_pos (log N/w))).mp
    calc (M * (N:ℝ)^(-2/w)) * exp (log N/w) < M := by
           rw [mul_assoc]
           simpa only [mul_one] using mul_lt_mul_of_pos_left sep mpos
         _ ≤ _ := mass
  · rw [ratio,Nat.coprime_mul_iff_left]
    exact ⟨cop.of_dvd_right (show m ∣ n/q by change m ∣ t; rw [← dm]; exact dvd_mul_left _ _),unit⟩

