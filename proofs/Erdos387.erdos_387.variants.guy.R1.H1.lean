import OMAReductions.R_Erdos387_erdos_387_variants_guy_R1

/-!
Proof of `OMA.R_Erdos387_erdos_387_variants_guy_R1.H1` (weight-two covering progression
extended to avoid all primes up to `2 * k`).

Strategy:
1. Reduce `H1` to the restricted prime covering problem on `{1, ..., k}` with allowed
   residues `b p = 0` or `k % p < b p < p`, using Kummer's theorem (`Nat.factorization_choose`)
   and `Nat.chineseRemainderOfFinset`.
2. Show that any prime cluster `(Q, f : Fin r → ℕ)` of primes `q ≡ 1 [MOD Q]` with
   `Q ^ r < f t`, `f 0 + Q - 1 < Q ^ (r + 1)`, `f 0 + Q - 1 < 2 * f t`, and
   `f 0 - f t ≤ Q ^ 2 - Q` yields a valid restricted cover for `k = f 0 + Q - 1`.
3. Prove a Brun-Titchmarsh type upper bound for primes `q ∈ (K, 3 * K]` with `p ^ a ∣ q - 1`
   (`p ^ a ≤ K ^ (3 / 5)`) via `BoundingSieve` (`Mathlib.NumberTheory.SelbergSieve`).
4. Double count `∑ q ∈ (Ioc K (3 * K)).filter Nat.Prime, Real.log (q - 1)` using
   `Chebyshev.theta_ge`, `Chebyshev.theta_le_log4_mul_x`, and pigeonhole on prime clusters
   to obtain a valid `k > K` for all sufficiently large `K`.
-/

namespace Erdos387H1B

open Finset Filter Real Nat ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta

/- ### Section 1: Reduction of H1 to the restricted covering problem -/

private def HasCover (k : ℕ) : Prop :=
  2 ≤ k ∧ ∃ b : ℕ → ℕ,
    (∀ p ≤ k, p.Prime → b p = 0 ∨ (k % p < b p ∧ b p < p)) ∧
    (∀ j, 1 ≤ j → j ≤ k → ∃ p ≤ k, p.Prime ∧ j ≡ b p [MOD p])

private lemma prod_dvd_of_pairwise_coprime {ι : Type*} (s : Finset ι) (f : ι → ℕ) (m : ℕ)
    (hcop : (s : Set ι).Pairwise (fun x y => Nat.Coprime (f x) (f y)))
    (hdvd : ∀ x ∈ s, f x ∣ m) : (∏ x ∈ s, f x) ∣ m := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [prod_insert ha]
    have hcop_s : (s : Set ι).Pairwise (fun x y => Nat.Coprime (f x) (f y)) :=
      hcop.mono (by simp)
    have h1 : f a ∣ m := hdvd a (mem_insert_self a s)
    have h2 : (∏ x ∈ s, f x) ∣ m := ih hcop_s (fun x hx => hdvd x (mem_insert_of_mem hx))
    have hca : Nat.Coprime (f a) (∏ x ∈ s, f x) :=
      Nat.coprime_prod_right_iff.mpr fun x hx =>
        hcop (mem_insert_self a s) (mem_insert_of_mem hx) (fun h => ha (h ▸ hx))
    exact hca.mul_dvd_of_dvd_of_dvd h1 h2

private lemma choose_factorization_eq_zero_of_digit {k p a : ℕ} (hp : p.Prime)
    (hka : k % p ≤ a) (hap : a < p) :
    let r := (k / p) * p + a
    (r.choose k).factorization p = 0 := by
  intro r
  have hkr : k ≤ r := by
    have hdiv := Nat.div_add_mod k p
    dsimp only [r]
    nlinarith
  have hrk : r - k = a - k % p := by
    have hdiv := Nat.div_add_mod k p
    rw [mul_comm] at hdiv
    dsimp only [r]
    omega
  rw [Nat.factorization_choose hp hkr (Nat.lt_add_one _)]
  rw [Finset.card_eq_zero, filter_eq_empty_iff]
  intro t ht
  rw [mem_Ico] at ht
  rw [not_le]
  have hpt_pos : 0 < p ^ t := pow_pos hp.pos t
  have hp_le_pt : p ≤ p ^ t := by
    calc p = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ t := Nat.pow_le_pow_right hp.pos ht.1
  have hrk_lt : r - k < p ^ t := by omega
  rw [Nat.mod_eq_of_lt hrk_lt, hrk]
  have hp_dvd_pt : p ∣ p ^ t := dvd_pow_self p (by omega)
  have hmod_mod : (k % p ^ t) % p = k % p := Nat.mod_mod_of_dvd k hp_dvd_pt
  have hdiv_pt : p ^ t = (p ^ (t - 1)) * p := by
    rw [← pow_succ, Nat.sub_add_cancel ht.1]
  have hq_lt : (k % p ^ t) / p < p ^ (t - 1) := by
    rw [Nat.div_lt_iff_lt_mul hp.pos, ← hdiv_pt]
    exact Nat.mod_lt k hpt_pos
  have hkm : k % p ^ t = ((k % p ^ t) / p) * p + k % p := by
    rw [← hmod_mod, mul_comm]
    exact (Nat.div_add_mod (k % p ^ t) p).symm
  have hle_pow : ((k % p ^ t) / p + 1) * p ≤ p ^ t := by
    conv_rhs => rw [hdiv_pt]
    exact Nat.mul_le_mul_right p hq_lt
  rw [add_mul, one_mul] at hle_pow
  omega

private lemma h1_witness_of_hasCover {k : ℕ} (hk : HasCover k) :
    ∃ γ : ℕ, ∃ g : ℕ → ℕ,
      (∀ i < k, 2 ≤ g i) ∧ (∏ i ∈ range k, g i) = k.factorial ∧
      ∀ n : ℕ, k < n → n ≡ γ [MOD (∏ p ∈ (2 * k).primesLE, p ^ (Nat.log p k + 1))] →
        (∀ i < k, g i ∣ n - i) ∧ ∀ p : ℕ, p.Prime → p ≤ 2 * k → ¬ p ∣ n.choose k := by
  obtain ⟨hk2, b, hb_allow, hb_cov⟩ := hk
  let a : ℕ → ℕ := fun p => if b p = 0 then k % p else p + k % p - b p
  let r : ℕ → ℕ := fun p => if p ≤ k then (k / p) * p + a p else k
  let e : ℕ → ℕ := fun p => Nat.log p k + 1
  have ha_bounds : ∀ p ≤ k, p.Prime → k % p ≤ a p ∧ a p < p := by
    intro p hpk hp
    dsimp only [a]
    rcases hb_allow p hpk hp with hb0 | ⟨h1, h2⟩
    · rw [if_pos hb0]
      exact ⟨le_rfl, Nat.mod_lt k hp.pos⟩
    · have hbne : b p ≠ 0 := by omega
      rw [if_neg hbne]
      omega
  have hr_ge : ∀ p, p.Prime → k ≤ r p := by
    intro p hp
    dsimp only [r]
    split_ifs with hpk
    · have h1 := (ha_bounds p hpk hp).1
      have hdiv := Nat.div_add_mod k p
      nlinarith
    · exact le_rfl
  have hr_lt : ∀ p, p.Prime → r p < p ^ e p := by
    intro p hp
    dsimp only [r, e]
    split_ifs with hpk
    · have h2 := (ha_bounds p hpk hp).2
      have hklt : k < p ^ (Nat.log p k + 1) := Nat.lt_pow_succ_log_self hp.one_lt k
      rw [pow_succ] at hklt ⊢
      have hq : k / p < p ^ Nat.log p k := (Nat.div_lt_iff_lt_mul hp.pos).mpr hklt
      have hq1 : (k / p + 1) * p ≤ p ^ Nat.log p k * p := Nat.mul_le_mul_right p hq
      rw [add_mul, one_mul] at hq1
      omega
    · exact Nat.lt_pow_succ_log_self hp.one_lt k
  have hr_choose : ∀ p ≤ k, p.Prime → ((r p).choose k).factorization p = 0 := by
    intro p hpk hp
    have h1 := ha_bounds p hpk hp
    dsimp only [r]
    rw [if_pos hpk]
    exact choose_factorization_eq_zero_of_digit hp h1.1 h1.2
  have hs_ne : ∀ p ∈ (2 * k).primesLE, p ^ e p ≠ 0 := fun p hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primesLE hp).ne_zero
  have hs_cop : ((2 * k).primesLE : Set ℕ).Pairwise (Function.onFun Nat.Coprime fun p => p ^ e p) := by
    intro p hp q hq hpq
    change Nat.Coprime (p ^ e p) (q ^ e q)
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primesLE hp)
      (Nat.prime_of_mem_primesLE hq)).mpr hpq).pow _ _
  let γ_sub := Nat.chineseRemainderOfFinset r (fun p => p ^ e p) (2 * k).primesLE hs_ne hs_cop
  let γ : ℕ := γ_sub.val
  let g : ℕ → ℕ := fun i => ∏ p ∈ k.primesLE, p ^ ((r p - i).factorization p)
  refine ⟨γ, g, ?_, ?_, ?_⟩
  · intro i hik
    have hj1 : 1 ≤ k - i := by omega
    have hjk : k - i ≤ k := Nat.sub_le k i
    obtain ⟨p, hpk, hp, hcong⟩ := hb_cov (k - i) hj1 hjk
    have hp_mem : p ∈ k.primesLE := Nat.mem_primesLE.mpr ⟨hpk, hp⟩
    have hr_i_pos : 0 < r p - i := by have := hr_ge p hp; omega
    have hp_dvd_ri : p ∣ r p - i := by
      have ha_cong : r p ≡ a p [MOD p] := by
        dsimp only [r]
        rw [if_pos hpk]
        change ((k / p) * p + a p) % p = a p % p
        rw [Nat.mul_add_mod_self_right]
      have hri_mod : i ≡ a p [MOD p] := by
        dsimp only [a]
        rcases hb_allow p hpk hp with hb0 | ⟨h1, h2⟩
        · rw [if_pos hb0]
          rw [hb0] at hcong
          have hadd : (k - i) + i = k := Nat.sub_add_cancel (le_of_lt hik)
          have h1' : (k - i) + i ≡ 0 + i [MOD p] := Nat.ModEq.add_right i hcong
          rw [hadd, zero_add] at h1'
          exact h1'.symm.trans (Nat.mod_modEq k p).symm
        · have hbne : b p ≠ 0 := by omega
          rw [if_neg hbne]
          have hadd : (k - i) + i = k := Nat.sub_add_cancel (le_of_lt hik)
          have h1' : (k - i) + i ≡ b p + i [MOD p] := Nat.ModEq.add_right i hcong
          rw [hadd] at h1'
          have h2' : (p + k % p - b p) + b p = p + k % p := by omega
          have h3' : b p + (p + k % p - b p) ≡ k [MOD p] := by
            rw [add_comm, h2']
            change (p + k % p) % p = k % p
            rw [Nat.add_mod_left, Nat.mod_mod]
          exact Nat.ModEq.add_left_cancel' (b p) (h1'.symm.trans h3'.symm)
      have hri2 : i ≡ r p [MOD p] := hri_mod.trans ha_cong.symm
      exact (Nat.modEq_iff_dvd' (by have := hr_ge p hp; omega)).mp hri2
    have hfac_pos : 1 ≤ (r p - i).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp hr_i_pos.ne' hp_dvd_ri
    have hp_dvd_g : p ∣ g i := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ∣ p ^ ((r p - i).factorization p) := Nat.pow_dvd_pow p hfac_pos
        _ ∣ g i := dvd_prod_of_mem _ hp_mem
    have hg_pos : 0 < g i := prod_pos fun q hq =>
      pow_pos (Nat.prime_of_mem_primesLE hq).pos _
    exact hp.two_le.trans (Nat.le_of_dvd hg_pos hp_dvd_g)
  · dsimp only [g]
    rw [Finset.prod_comm]
    have hinner : ∀ p ∈ k.primesLE,
        (∏ i ∈ range k, p ^ ((r p - i).factorization p)) = p ^ (k.factorial.factorization p) := by
      intro p hp_mem
      have hp := Nat.prime_of_mem_primesLE hp_mem
      have hpk := Nat.le_of_mem_primesLE hp_mem
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      have hne : ∀ i ∈ range k, r p - i ≠ 0 := by
        intro i hi
        have := hr_ge p hp
        have := mem_range.mp hi
        omega
      have hprod_fac := Nat.factorization_prod hne
      have hsum_eq : ∑ i ∈ range k, (r p - i).factorization p =
          (∏ i ∈ range k, (r p - i)).factorization p := by
        rw [hprod_fac, Finsupp.finsetSum_apply]
      rw [hsum_eq, ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
      have hch_ne : (r p).choose k ≠ 0 := Nat.choose_ne_zero (hr_ge p hp)
      rw [Nat.factorization_mul k.factorial_ne_zero hch_ne, Finsupp.coe_add, Pi.add_apply,
        hr_choose p hpk hp, add_zero]
    rw [Finset.prod_congr rfl hinner]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self k.factorial_ne_zero]
    rw [Finsupp.prod]
    symm
    apply Finset.prod_subset
    · intro p hp
      rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
      exact Nat.mem_primesLE.mpr ⟨(Nat.Prime.dvd_factorial hp.1).mp hp.2.1, hp.1⟩
    · intro p _ hp_nmem
      rw [Finsupp.mem_support_iff, Classical.not_not] at hp_nmem
      simp [hp_nmem]
  · intro n hkn hnγ
    have hn_mod_p : ∀ p ∈ (2 * k).primesLE, n ≡ r p [MOD p ^ e p] := by
      intro p hp_mem
      have hdvd : p ^ e p ∣ ∏ q ∈ (2 * k).primesLE, q ^ e q :=
        dvd_prod_of_mem (fun q => q ^ e q) hp_mem
      exact (hnγ.of_dvd hdvd).trans (γ_sub.prop p hp_mem)
    have hfac_eq : ∀ p ∈ k.primesLE, ∀ i < k,
        (n - i).factorization p = (r p - i).factorization p := by
      intro p hp_mem i hik
      have hp := Nat.prime_of_mem_primesLE hp_mem
      have hpk := Nat.le_of_mem_primesLE hp_mem
      have hp2k : p ∈ (2 * k).primesLE := Nat.mem_primesLE.mpr ⟨by omega, hp⟩
      have hmod_pe : n ≡ r p [MOD p ^ e p] := hn_mod_p p hp2k
      have hri_pos : 0 < r p - i := by have := hr_ge p hp; omega
      have hni_pos : 0 < n - i := by omega
      have hri_lt : r p - i < p ^ e p := lt_of_le_of_lt (Nat.sub_le _ _) (hr_lt p hp)
      set v := (r p - i).factorization p
      have hv_lt : v < e p := by
        by_contra! hge
        have h1 : p ^ e p ∣ p ^ v := Nat.pow_dvd_pow p hge
        have h2 : p ^ v ∣ r p - i := Nat.ordProj_dvd (r p - i) p
        have h3 := Nat.le_of_dvd hri_pos (h1.trans h2)
        omega
      have hsub_mod : n - i ≡ r p - i [MOD p ^ e p] := by
        apply Nat.ModEq.add_right_cancel' i
        rw [Nat.sub_add_cancel (le_of_lt (hik.trans hkn)),
          Nat.sub_add_cancel (le_of_lt (lt_of_lt_of_le hik (hr_ge p hp)))]
        exact hmod_pe
      have hdvd_v : p ^ v ∣ n - i := by
        have h1 : p ^ v ∣ p ^ e p := Nat.pow_dvd_pow p hv_lt.le
        have h2 : n - i ≡ r p - i [MOD p ^ v] := hsub_mod.of_dvd h1
        have h3 : p ^ v ∣ r p - i := Nat.ordProj_dvd (r p - i) p
        exact Nat.dvd_iff_mod_eq_zero.mpr (Eq.trans h2 (Nat.dvd_iff_mod_eq_zero.mp h3))
      have hndvd_v1 : ¬ p ^ (v + 1) ∣ n - i := by
        intro hd
        have h1 : p ^ (v + 1) ∣ p ^ e p := Nat.pow_dvd_pow p hv_lt
        have h2 : n - i ≡ r p - i [MOD p ^ (v + 1)] := hsub_mod.of_dvd h1
        have h3 : p ^ (v + 1) ∣ r p - i :=
          Nat.dvd_iff_mod_eq_zero.mpr (Eq.trans h2.symm (Nat.dvd_iff_mod_eq_zero.mp hd))
        exact Nat.pow_succ_factorization_not_dvd hri_pos.ne' hp h3
      have hle1 : v ≤ (n - i).factorization p :=
        (hp.pow_dvd_iff_le_factorization hni_pos.ne').mp hdvd_v
      have hle2 : ¬ v + 1 ≤ (n - i).factorization p := by
        intro h
        exact hndvd_v1 ((hp.pow_dvd_iff_le_factorization hni_pos.ne').mpr h)
      omega
    constructor
    · intro i hik
      apply prod_dvd_of_pairwise_coprime k.primesLE (fun p => p ^ ((r p - i).factorization p))
      · intro p hp q hq hpq
        exact ((Nat.coprime_primes (Nat.prime_of_mem_primesLE hp)
          (Nat.prime_of_mem_primesLE hq)).mpr hpq).pow _ _
      · intro p hp_mem
        rw [← hfac_eq p hp_mem i hik]
        exact Nat.ordProj_dvd (n - i) p
    · intro p hp hp2k hdvd_ch
      have hp_mem2k : p ∈ (2 * k).primesLE := Nat.mem_primesLE.mpr ⟨hp2k, hp⟩
      by_cases hpk : p ≤ k
      · have hp_memk : p ∈ k.primesLE := Nat.mem_primesLE.mpr ⟨hpk, hp⟩
        have hch_pos : n.choose k ≠ 0 := Nat.choose_ne_zero hkn.le
        have hfac_ch_pos : 0 < (n.choose k).factorization p :=
          Nat.Prime.factorization_pos_of_dvd hp hch_pos hdvd_ch
        have hne_n : ∀ i ∈ range k, n - i ≠ 0 := by
          intro i hi; have := mem_range.mp hi; omega
        have hne_r : ∀ i ∈ range k, r p - i ≠ 0 := by
          intro i hi; have := mem_range.mp hi; have := hr_ge p hp; omega
        have hsum_n : (∏ i ∈ range k, (n - i)).factorization p =
            (∏ i ∈ range k, (r p - i)).factorization p := by
          rw [Nat.factorization_prod hne_n, Nat.factorization_prod hne_r,
            Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
          exact Finset.sum_congr rfl fun i hi => hfac_eq p hp_memk i (mem_range.mp hi)
        rw [← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
          Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
          Nat.factorization_mul k.factorial_ne_zero hch_pos,
          Nat.factorization_mul k.factorial_ne_zero (Nat.choose_ne_zero (hr_ge p hp)),
          Finsupp.coe_add, Finsupp.coe_add, Pi.add_apply, Pi.add_apply,
          hr_choose p hpk hp, add_zero] at hsum_n
        omega
      · have hkp : k < p := by omega
        have he1 : e p = 1 := by
          dsimp only [e]
          rw [Nat.log_eq_zero_iff.mpr (Or.inl hkp)]
        have hrk : r p = k := by dsimp only [r]; rw [if_neg hpk]
        have hn_mod_p' : n ≡ k [MOD p] := by
          have := hn_mod_p p hp_mem2k
          rwa [he1, pow_one, hrk] at this
        have hp_dvd_desc : p ∣ n.descFactorial k := by
          rw [Nat.descFactorial_eq_factorial_mul_choose]
          exact dvd_mul_of_dvd_right hdvd_ch _
        rw [Nat.descFactorial_eq_prod_range] at hp_dvd_desc
        obtain ⟨i, hi, hp_dvd_ni⟩ := (hp.prime.dvd_finsetProd_iff _).mp hp_dvd_desc
        have hik : i < k := mem_range.mp hi
        have hsub : n - i ≡ k - i [MOD p] := by
          apply Nat.ModEq.add_right_cancel' i
          rw [Nat.sub_add_cancel (le_of_lt (hik.trans hkn)), Nat.sub_add_cancel hik.le]
          exact hn_mod_p'
        have hp_dvd_ki : p ∣ k - i :=
          Nat.dvd_iff_mod_eq_zero.mpr (Eq.trans hsub.symm (Nat.dvd_iff_mod_eq_zero.mp hp_dvd_ni))
        have hle := Nat.le_of_dvd (by omega) hp_dvd_ki
        omega

private lemma h1_of_frequently_hasCover (h : ∃ᶠ k : ℕ in atTop, HasCover k) :
    OMA.R_Erdos387_erdos_387_variants_guy_R1.H1 :=
  h.mono fun _ hk => h1_witness_of_hasCover hk

/- ### Section 2: Combinatorial prime-cluster lemma -/

private lemma hasCover_of_prime_cluster {Q r : ℕ} (hQ : Q.Prime) (hr : 1 ≤ r)
    (f : Fin r → ℕ) (hf_inj : Function.Injective f)
    (hf_prime : ∀ t, (f t).Prime)
    (hf_dvd : ∀ t, Q ∣ f t - 1)
    (hf_le : ∀ t, f t ≤ f ⟨0, hr⟩)
    (hQr_lt : ∀ t, Q ^ r < f t)
    (hk_lt : f ⟨0, hr⟩ + Q - 1 < Q ^ (r + 1))
    (hk_lt_two : ∀ t, f ⟨0, hr⟩ + Q - 1 < 2 * f t)
    (hdiff : ∀ t, f ⟨0, hr⟩ - f t ≤ Q ^ 2 - Q) :
    HasCover (f ⟨0, hr⟩ + Q - 1) := by
  set k := f ⟨0, hr⟩ + Q - 1
  have hQ2 : 2 ≤ Q := hQ.two_le
  have hf0_gt_Q : Q < f ⟨0, hr⟩ := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ r := Nat.pow_le_pow_right hQ.pos hr
      _ < f ⟨0, hr⟩ := hQr_lt ⟨0, hr⟩
  have hk2 : 2 ≤ k := by dsimp only [k]; omega
  let b : ℕ → ℕ := fun p =>
    if p = Q then 1
    else if h : ∃ t : Fin r, f t = p then Q ^ ((Classical.choose h).val + 1)
    else 0
  refine ⟨hk2, b, ?_, ?_⟩
  · intro p hpk hp
    dsimp only [b]
    by_cases hpQ : p = Q
    · rw [if_pos hpQ]
      right
      subst hpQ
      have hQ_dvd_k : p ∣ k := by
        have h1 : p ∣ f ⟨0, hr⟩ - 1 := hf_dvd ⟨0, hr⟩
        have h2 : k = (f ⟨0, hr⟩ - 1) + p := by dsimp only [k]; omega
        rw [h2]
        exact dvd_add h1 dvd_rfl
      rw [Nat.mod_eq_zero_of_dvd hQ_dvd_k]
      exact ⟨by omega, hp.one_lt⟩
    · rw [if_neg hpQ]
      by_cases hex : ∃ t : Fin r, f t = p
      · rw [dif_pos hex]
        right
        set t := Classical.choose hex
        have hft : f t = p := Classical.choose_spec hex
        have hp_lt_k : p < k := by
          have := hf_le t
          dsimp only [k]
          omega
        have hk_lt_2p : k < 2 * p := hft ▸ hk_lt_two t
        have hk_mod_p : k % p = k - p := by
          have h1 : k = p + (k - p) := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hk_mod_p]
        constructor
        · by_cases ht0 : t.val = 0
          · have hteq : t = ⟨0, hr⟩ := Fin.ext ht0
            rw [hteq] at hft
            rw [ht0, zero_add, pow_one, ← hft]
            dsimp only [k]
            omega
          · have hQ2_le : Q ^ 2 ≤ Q ^ (t.val + 1) :=
              Nat.pow_le_pow_right hQ.pos (by omega)
            have hd := hdiff t
            have hle := hf_le t
            have hQ2_ge : Q ≤ Q ^ 2 := by nlinarith
            dsimp only [k]
            omega
        · calc Q ^ (t.val + 1) ≤ Q ^ r := Nat.pow_le_pow_right hQ.pos t.isLt
            _ < f t := hQr_lt t
            _ = p := hft
      · rw [dif_neg hex]
        exact Or.inl rfl
  · intro j hj1 hjk
    have hQ_le_k : Q ≤ k := by dsimp only [k]; omega
    have hQ_ne_f : ∀ t : Fin r, f t ≠ Q := by
      intro t h
      have := hQr_lt t
      have h1 : Q ≤ Q ^ r := by
        calc Q = Q ^ 1 := (pow_one Q).symm
          _ ≤ Q ^ r := Nat.pow_le_pow_right hQ.pos hr
      omega
    by_cases hj_one : j = 1
    · refine ⟨Q, hQ_le_k, hQ, ?_⟩
      dsimp only [b]
      rw [if_pos rfl, hj_one]
    by_cases hj_img : ∃ t : Fin r, f t = j
    · obtain ⟨t, hft⟩ := hj_img
      refine ⟨Q, hQ_le_k, hQ, ?_⟩
      dsimp only [b]
      rw [if_pos rfl, ← hft]
      have h1 : 1 ≤ f t := (hf_prime t).one_le
      exact ((Nat.modEq_iff_dvd' h1).mpr (hf_dvd t)).symm
    by_cases hj_pow : ∃ a : ℕ, 1 ≤ a ∧ j = Q ^ a
    · obtain ⟨a, ha1, rfl⟩ := hj_pow
      have har : a ≤ r := by
        by_contra! hgt
        have : Q ^ (r + 1) ≤ Q ^ a := Nat.pow_le_pow_right hQ.pos hgt
        omega
      let t : Fin r := ⟨a - 1, by omega⟩
      have hft_le_k : f t ≤ k := by have := hf_le t; dsimp only [k]; omega
      refine ⟨f t, hft_le_k, hf_prime t, ?_⟩
      dsimp only [b]
      rw [if_neg (hQ_ne_f t)]
      have hex : ∃ s : Fin r, f s = f t := ⟨t, rfl⟩
      rw [dif_pos hex]
      have hch : Classical.choose hex = t := hf_inj (Classical.choose_spec hex)
      rw [hch]
      have hta : t.val + 1 = a := by dsimp only [t]; omega
      rw [hta]
    · have hj2 : 2 ≤ j := by omega
      have hex_p : ∃ p, p.Prime ∧ p ∣ j ∧ p ≠ Q := by
        by_contra! hall
        have hj_ne0 : j ≠ 0 := by omega
        have hsub : j.primeFactors ⊆ {Q} := by
          intro p hp
          rw [Nat.mem_primeFactors] at hp
          exact mem_singleton.mpr (hall p hp.1 hp.2.1)
        have hj_eq : j = Q ^ (j.factorization Q) := by
          conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hj_ne0]
          rw [Finsupp.prod]
          have hsupp : j.factorization.support ⊆ {Q} := by
            rwa [Nat.support_factorization]
          rw [Finset.prod_subset hsupp (fun x _ hx => by
            rw [Finsupp.mem_support_iff, Classical.not_not] at hx; simp [hx])]
          simp
        have hfac_pos : 1 ≤ j.factorization Q := by
          by_contra! h0
          have h0' : j.factorization Q = 0 := by omega
          rw [h0', pow_zero] at hj_eq
          omega
        exact hj_pow ⟨j.factorization Q, hfac_pos, hj_eq⟩
      obtain ⟨p, hp, hp_dvd_j, hpQ⟩ := hex_p
      have hp_not_f : ¬ ∃ t : Fin r, f t = p := by
        rintro ⟨t, rfl⟩
        have hne : f t ≠ j := fun h => hj_img ⟨t, h⟩
        obtain ⟨c, rfl⟩ := hp_dvd_j
        have hc2 : 2 ≤ c := by
          rcases c with _ | _ | c
          · simp at hj1
          · simp at hne
          · omega
        have h2ft : 2 * f t ≤ f t * c := by nlinarith
        have := hk_lt_two t
        omega
      refine ⟨p, (Nat.le_of_dvd (by omega) hp_dvd_j).trans hjk, hp, ?_⟩
      dsimp only [b]
      rw [if_neg hpQ, dif_neg hp_not_f]
      exact Nat.modEq_zero_iff_dvd.mpr hp_dvd_j

/- ### Section 3: Selberg Sieve Brun-Titchmarsh upper bound -/

private noncomputable def invId : ArithmeticFunction ℝ where
  toFun := fun n => if n = 0 then 0 else (n : ℝ)⁻¹
  map_zero' := by simp

private lemma invId_isMultiplicative : invId.IsMultiplicative := by
  refine ⟨by simp [invId], fun {a b} _ => ?_⟩
  dsimp only [invId, ArithmeticFunction.coe_mk]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp only [mul_eq_zero, ha, hb, or_self, ↓reduceIte, Nat.cast_mul, mul_inv]

private lemma card_Ioc_modEq_eq (K M c : ℕ) (hM : 0 < M) (hc : c < M) :
    ((Ioc K (3 * K)).filter (fun n => n % M = c)).card =
      (3 * K + M - c) / M - (K + M - c) / M := by
  have hIcc : ∀ A : ℕ, ((Icc 0 A).filter (fun n => n % M = c)).card = (A + M - c) / M := by
    intro A
    have hbij : ((Icc 0 A).filter (fun n => n % M = c)) =
        (range ((A + M - c) / M)).image (fun t => t * M + c) := by
      ext n
      simp only [mem_filter, mem_Icc, Nat.zero_le, true_and, mem_image, mem_range]
      constructor
      · intro ⟨hnA, hnmod⟩
        refine ⟨n / M, ?_, ?_⟩
        · rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hM, add_mul, one_mul]
          have hdiv := Nat.div_add_mod n M
          rw [mul_comm] at hdiv
          omega
        · rw [mul_comm, ← hnmod]
          exact Nat.div_add_mod n M
      · rintro ⟨t, ht, rfl⟩
        rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hM, add_mul, one_mul] at ht
        constructor
        · omega
        · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc]
    rw [hbij, Finset.card_image_of_injective]
    · exact card_range _
    · intro x y hxy
      dsimp only at hxy
      have : x * M = y * M := by omega
      exact Nat.eq_of_mul_eq_mul_right hM this
  have hdisj : Disjoint ((Icc 0 K).filter (fun n => n % M = c))
      ((Ioc K (3 * K)).filter (fun n => n % M = c)) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [mem_filter, mem_Icc, mem_Ioc] at hn1 hn2
    omega
  have hunion : ((Icc 0 K).filter (fun n => n % M = c)) ∪
      ((Ioc K (3 * K)).filter (fun n => n % M = c)) =
      (Icc 0 (3 * K)).filter (fun n => n % M = c) := by
    ext n
    simp only [mem_union, mem_filter, mem_Icc, mem_Ioc]
    omega
  have hcard := card_union_of_disjoint hdisj
  rw [hunion, hIcc (3 * K), hIcc K] at hcard
  omega

private lemma abs_card_Ioc_modEq_sub_le_one (K M c : ℕ) (hM : 0 < M) (hc : c < M) :
    |(((Ioc K (3 * K)).filter (fun n => n % M = c)).card : ℝ) - (2 * K : ℝ) / (M : ℝ)| ≤ 1 := by
  rw [card_Ioc_modEq_eq K M c hM hc]
  have hle : (K + M - c) / M ≤ (3 * K + M - c) / M := Nat.div_le_div_right (by omega)
  rw [Nat.cast_sub hle]
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have h1 : ∀ A : ℕ, ((A + M - c : ℕ) : ℝ) / M - 1 < (((A + M - c) / M : ℕ) : ℝ) ∧
      (((A + M - c) / M : ℕ) : ℝ) ≤ ((A + M - c : ℕ) : ℝ) / M := by
    intro A
    have hmod := Nat.div_add_mod (A + M - c) M
    have hlt := Nat.mod_lt (A + M - c) hM
    have hcast : ((A + M - c : ℕ) : ℝ) =
        M * (((A + M - c) / M : ℕ) : ℝ) + (((A + M - c) % M : ℕ) : ℝ) := by
      exact_mod_cast hmod.symm
    have hltR : (((A + M - c) % M : ℕ) : ℝ) < M := by exact_mod_cast hlt
    have hnnR : (0 : ℝ) ≤ (((A + M - c) % M : ℕ) : ℝ) := Nat.cast_nonneg _
    constructor
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hMpos]
      linarith
    · rw [le_div_iff₀ hMpos]
      linarith
  obtain ⟨h3l, h3u⟩ := h1 (3 * K)
  obtain ⟨h1l, h1u⟩ := h1 K
  have hdiff : ((3 * K + M - c : ℕ) : ℝ) / M - ((K + M - c : ℕ) : ℝ) / M = (2 * K : ℝ) / M := by
    have hc1 : c ≤ K + M := by omega
    have hc3 : c ≤ 3 * K + M := by omega
    rw [Nat.cast_sub hc3, Nat.cast_sub hc1]
    push_cast
    ring
  rw [abs_le]
  constructor <;> linarith

private lemma harmonic_ge_log_succ (z : ℕ) :
    Real.log (z + 1 : ℝ) ≤ ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ := by
  induction z with
  | zero => simp
  | succ z ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ z + 1)]
    have hstep : Real.log ((z + 1 : ℕ) + 1 : ℝ) - Real.log ((z + 1 : ℕ) : ℝ) ≤
        ((z + 1 : ℕ) : ℝ)⁻¹ := by
      rw [← Real.log_div (by positivity) (by positivity)]
      have hdiv : (((z + 1 : ℕ) + 1 : ℝ) / ((z + 1 : ℕ) : ℝ)) = 1 + ((z + 1 : ℕ) : ℝ)⁻¹ := by
        field_simp
      rw [hdiv]
      linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + ((z + 1 : ℕ) : ℝ)⁻¹ by positivity)]
    push_cast at hstep ⊢
    linarith

private lemma sum_inv_le_prod_inv_one_sub (S : Finset ℕ) (hS : ∀ r ∈ S, r.Prime) :
    ∀ B : Finset ℕ, (∀ m ∈ B, m ≠ 0 ∧ m.primeFactors ⊆ S) →
      ∑ m ∈ B, (m : ℝ)⁻¹ ≤ ∏ r ∈ S, (1 - (r : ℝ)⁻¹)⁻¹ := by
  induction S using Finset.induction_on with
  | empty =>
    intro B hB
    rw [prod_empty]
    have hsub : B ⊆ {1} := by
      intro m hm
      obtain ⟨hm0, hpf⟩ := hB m hm
      rw [mem_singleton]
      by_contra hm1
      have hne : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
      obtain ⟨r, hr⟩ := hne
      exact absurd (hpf hr) (notMem_empty r)
    calc ∑ m ∈ B, (m : ℝ)⁻¹ ≤ ∑ m ∈ ({1} : Finset ℕ), (m : ℝ)⁻¹ :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by simp
  | @insert q S hqS ih =>
    intro B hB
    have hq : q.Prime := hS q (mem_insert_self q S)
    have hS' : ∀ r ∈ S, r.Prime := fun r hr => hS r (mem_insert_of_mem hr)
    let E := B.sup (fun m => m.factorization q) + 1
    have hmaps : ∀ m ∈ B, m.factorization q ∈ range E := fun m hm =>
      mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := fun m => m.factorization q) hm))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, prod_insert hqS]
    have hfiber : ∀ e ∈ range E,
        ∑ m ∈ B.filter (fun m => m.factorization q = e), (m : ℝ)⁻¹ ≤
          ((q : ℝ)⁻¹) ^ e * ∏ r ∈ S, (1 - (r : ℝ)⁻¹)⁻¹ := by
      intro e _
      set Be := B.filter (fun m => m.factorization q = e)
      set B' := Be.image (fun m => m / q ^ e)
      have hdiv_eq : ∀ m ∈ Be, m = q ^ e * (m / q ^ e) := by
        intro m hm
        have he : m.factorization q = e := (mem_filter.mp hm).2
        have hd : q ^ e ∣ m := he ▸ Nat.ordProj_dvd m q
        exact (Nat.mul_div_cancel' hd).symm
      have hinj : Set.InjOn (fun m => m / q ^ e) Be := by
        intro x hx y hy hxy
        dsimp only at hxy
        rw [hdiv_eq x hx, hdiv_eq y hy, hxy]
      have hsum_eq : ∑ m ∈ Be, (m : ℝ)⁻¹ = ((q : ℝ)⁻¹) ^ e * ∑ m' ∈ B', (m' : ℝ)⁻¹ := by
        rw [Finset.mul_sum, Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun m hm => ?_
        conv_lhs => rw [hdiv_eq m hm]
        push_cast
        rw [mul_inv, inv_pow]
      rw [hsum_eq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply ih hS' B'
      intro m' hm'
      obtain ⟨m, hm, rfl⟩ := mem_image.mp hm'
      obtain ⟨hmB, hme⟩ := mem_filter.mp hm
      obtain ⟨hm0, hmpf⟩ := hB m hmB
      have hmeq : m = q ^ e * (m / q ^ e) := hdiv_eq m hm
      have hm'0 : m / q ^ e ≠ 0 := by
        intro h0; rw [h0, mul_zero] at hmeq; exact hm0 hmeq
      refine ⟨hm'0, ?_⟩
      intro r hr
      rw [Nat.mem_primeFactors] at hr
      have hr_dvd_m : r ∣ m := hr.2.1.trans ⟨q ^ e, by rw [mul_comm, ← hmeq]⟩
      have hr_in : r ∈ insert q S := hmpf (Nat.mem_primeFactors.mpr ⟨hr.1, hr_dvd_m, hm0⟩)
      rcases mem_insert.mp hr_in with hrq | hrS
      · exfalso
        rw [hrq] at hr
        have hqe1 : q ^ (e + 1) ∣ m := by
          rw [hmeq, pow_succ]
          exact mul_dvd_mul_left (q ^ e) hr.2.1
        have hle := (hq.pow_dvd_iff_le_factorization hm0).mp hqe1
        omega
      · exact hrS
    calc ∑ e ∈ range E, ∑ m ∈ B.filter (fun m => m.factorization q = e), (m : ℝ)⁻¹
        ≤ ∑ e ∈ range E, ((q : ℝ)⁻¹) ^ e * ∏ r ∈ S, (1 - (r : ℝ)⁻¹)⁻¹ :=
          Finset.sum_le_sum hfiber
      _ = (∑ e ∈ range E, ((q : ℝ)⁻¹) ^ e) * ∏ r ∈ S, (1 - (r : ℝ)⁻¹)⁻¹ := by
          rw [← Finset.sum_mul]
      _ ≤ (1 - (q : ℝ)⁻¹)⁻¹ * ∏ r ∈ S, (1 - (r : ℝ)⁻¹)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _
          · apply Finset.prod_nonneg
            intro r hr
            have h1 : (r : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (hS' r hr).one_lt)
            exact inv_nonneg.mpr (by linarith)
          · have hq_lt : (q : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)
            have hpow_nn : (0 : ℝ) ≤ (q : ℝ)⁻¹ ^ E := by positivity
            rw [geom_sum_eq hq_lt.ne, ← neg_div_neg_eq, neg_sub, neg_sub,
              div_le_iff₀ (by linarith : (0 : ℝ) < 1 - (q : ℝ)⁻¹)]
            have hinv : (1 - (q : ℝ)⁻¹)⁻¹ * (1 - (q : ℝ)⁻¹) = 1 :=
              inv_mul_cancel₀ (by linarith)
            linarith

private lemma selberg_G_ge_log {z p : ℕ} (hp : p.Prime)
    (s : BoundingSieve)
    (hP : s.prodPrimes = ∏ r ∈ z.primesLE.filter (· ≠ p), r)
    (hnu : s.nu = invId) :
    (1 / 2 : ℝ) * Real.log (z + 1 : ℝ) ≤
      ∑ l ∈ s.prodPrimes.divisors.filter (· ≤ z), s.selbergTerms l := by
  set S := s.prodPrimes.divisors.filter (· ≤ z)
  set A := (Icc 1 z).filter (fun n => ¬ p ∣ n)
  let rad : ℕ → ℕ := fun n => ∏ r ∈ n.primeFactors, r
  have hrad_dvd : ∀ n : ℕ, n ≠ 0 → rad n ∣ n := by
    intro n hn0
    apply prod_dvd_of_pairwise_coprime n.primeFactors id n
    · intro x hx y hy hxy
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hx)
        (Nat.prime_of_mem_primeFactors hy)).mpr hxy
    · intro x hx
      exact Nat.dvd_of_mem_primeFactors hx
  have hmaps : ∀ n ∈ A, rad n ∈ S := by
    intro n hn
    simp only [A, mem_filter, mem_Icc] at hn
    have hn0 : n ≠ 0 := by omega
    simp only [S, mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, s.prodPrimes_ne_zero⟩, (Nat.le_of_dvd (by omega) (hrad_dvd n hn0)).trans hn.1.2⟩
    rw [hP]
    apply Finset.prod_dvd_prod_of_subset
    intro r hr
    rw [Nat.mem_primeFactors] at hr
    rw [mem_filter, Nat.mem_primesLE]
    refine ⟨⟨(Nat.le_of_dvd (by omega) hr.2.1).trans hn.1.2, hr.1⟩, ?_⟩
    rintro rfl
    exact hn.2 hr.2.1
  have hfiber : ∑ n ∈ A, (n : ℝ)⁻¹ ≤ ∑ l ∈ S, s.selbergTerms l := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    apply Finset.sum_le_sum
    intro l hl
    simp only [S, mem_filter, Nat.mem_divisors] at hl
    have hl_sq : Squarefree l := s.squarefree_of_dvd_prodPrimes hl.1.1
    have hl0 : l ≠ 0 := hl_sq.ne_zero
    set Fl := A.filter (fun n => rad n = l)
    set B := Fl.image (fun n => n / l)
    have hdiv_eq : ∀ n ∈ Fl, n = l * (n / l) := by
      intro n hn
      have hnA := (mem_filter.mp hn).1
      have hradl : rad n = l := (mem_filter.mp hn).2
      have hn0 : n ≠ 0 := by simp only [A, mem_filter, mem_Icc] at hnA; omega
      exact (Nat.mul_div_cancel' (hradl ▸ hrad_dvd n hn0)).symm
    have hinj : Set.InjOn (fun n => n / l) Fl := by
      intro x hx y hy hxy
      dsimp only at hxy
      rw [hdiv_eq x hx, hdiv_eq y hy, hxy]
    have hsum_eq : ∑ n ∈ Fl, (n : ℝ)⁻¹ = (l : ℝ)⁻¹ * ∑ m ∈ B, (m : ℝ)⁻¹ := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun n hn => ?_
      conv_lhs => rw [hdiv_eq n hn]
      push_cast
      rw [mul_inv]
    rw [hsum_eq, BoundingSieve.selbergTerms_apply, hnu]
    simp only [invId, ArithmeticFunction.coe_mk, hl0, ↓reduceIte]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hprod_eq : ∏ r ∈ l.primeFactors, (1 - if r = 0 then (0 : ℝ) else (r : ℝ)⁻¹)⁻¹ =
        ∏ r ∈ l.primeFactors, (1 - (r : ℝ)⁻¹)⁻¹ := by
      refine Finset.prod_congr rfl fun r hr => ?_
      have hr0 : r ≠ 0 := (Nat.prime_of_mem_primeFactors hr).ne_zero
      simp [hr0]
    rw [hprod_eq]
    apply sum_inv_le_prod_inv_one_sub l.primeFactors
      (fun r hr => Nat.prime_of_mem_primeFactors hr) B
    intro m hm
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hm
    have hnA := (mem_filter.mp hn).1
    have hradl : rad n = l := (mem_filter.mp hn).2
    have hn0 : n ≠ 0 := by simp only [A, mem_filter, mem_Icc] at hnA; omega
    have hneq : n = l * (n / l) := hdiv_eq n hn
    have hm0 : n / l ≠ 0 := by intro h0; rw [h0, mul_zero] at hneq; exact hn0 hneq
    refine ⟨hm0, ?_⟩
    intro r hr
    rw [Nat.mem_primeFactors] at hr
    have hr_dvd_n : r ∣ n := hr.2.1.trans ⟨l, by rw [mul_comm, ← hneq]⟩
    have hr_pf_n : r ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hr.1, hr_dvd_n, hn0⟩
    have hr_dvd_l : r ∣ l := hradl ▸ dvd_prod_of_mem id hr_pf_n
    exact Nat.mem_primeFactors.mpr ⟨hr.1, hr_dvd_l, hl0⟩
  have hA_ge : (1 / 2 : ℝ) * ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ ≤ ∑ n ∈ A, (n : ℝ)⁻¹ := by
    have hsplit : ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ =
        ∑ n ∈ A, (n : ℝ)⁻¹ + ∑ n ∈ (Icc 1 z).filter (fun n => p ∣ n), (n : ℝ)⁻¹ := by
      rw [add_comm]
      exact (Finset.sum_filter_add_sum_filter_not (Icc 1 z) (fun n => p ∣ n) _).symm
    have hmult : ∑ n ∈ (Icc 1 z).filter (fun n => p ∣ n), (n : ℝ)⁻¹ =
        (p : ℝ)⁻¹ * ∑ j ∈ Icc 1 (z / p), (j : ℝ)⁻¹ := by
      have hbij : (Icc 1 z).filter (fun n => p ∣ n) = (Icc 1 (z / p)).image (fun j => p * j) := by
        ext n
        simp only [mem_filter, mem_Icc, mem_image]
        constructor
        · rintro ⟨⟨hn1, hnz⟩, ⟨j, rfl⟩⟩
          refine ⟨j, ⟨?_, ?_⟩, rfl⟩
          · rcases j with _ | j
            · simp at hn1
            · omega
          · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by linarith)
        · rintro ⟨j, ⟨hj1, hjp⟩, rfl⟩
          refine ⟨⟨?_, ?_⟩, dvd_mul_right p j⟩
          · have := hp.one_le; nlinarith
          · have := (Nat.le_div_iff_mul_le hp.pos).mp hjp; linarith
      rw [hbij, Finset.mul_sum, Finset.sum_image]
      · refine Finset.sum_congr rfl fun j _ => ?_
        push_cast; rw [mul_inv]
      · intro x _ y _ hxy
        exact Nat.eq_of_mul_eq_mul_left hp.pos hxy
    have hsub_le : ∑ j ∈ Icc 1 (z / p), (j : ℝ)⁻¹ ≤ ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self z p))
        fun _ _ _ => by positivity
    have hp_inv_le : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast hp.two_le)
    have h1 : (p : ℝ)⁻¹ * ∑ j ∈ Icc 1 (z / p), (j : ℝ)⁻¹ ≤
        (1 / 2 : ℝ) * ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ :=
      mul_le_mul hp_inv_le hsub_le (Finset.sum_nonneg fun _ _ => by positivity) (by norm_num)
    linarith
  calc (1 / 2 : ℝ) * Real.log (z + 1 : ℝ)
      ≤ (1 / 2 : ℝ) * ∑ n ∈ Icc 1 z, (n : ℝ)⁻¹ := by
        linarith [harmonic_ge_log_succ z]
    _ ≤ ∑ n ∈ A, (n : ℝ)⁻¹ := hA_ge
    _ ≤ ∑ l ∈ S, s.selbergTerms l := hfiber

private lemma selberg_siftedSum_le {z : ℕ} (hz : 1 ≤ z) (s : BoundingSieve)
    (_hX : 0 ≤ s.totalMass) (hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ 1) :
    let G := ∑ l ∈ s.prodPrimes.divisors.filter (· ≤ z), s.selbergTerms l
    s.siftedSum ≤ s.totalMass / G + (z : ℝ) ^ 2 := by
  intro G
  have h1_mem : 1 ∈ s.prodPrimes.divisors.filter (· ≤ z) := by
    simp only [mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, s.prodPrimes_ne_zero⟩, hz⟩
  have hG_pos : 0 < G := by
    refine Finset.sum_pos' (fun l hl => ?_) ⟨1, h1_mem, ?_⟩
    · exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hl).1)).le
    · exact s.selbergTerms_pos (one_dvd _)
  let w : ℕ → ℝ := fun d =>
    if d ∣ s.prodPrimes ∧ d ≤ z then
      (μ d : ℝ) / (G * s.nu d) *
        ∑ r ∈ s.prodPrimes.divisors.filter (fun r => d ∣ r ∧ r ≤ z), s.selbergTerms r
    else 0
  have hw1 : w 1 = 1 := by
    dsimp only [w]
    rw [if_pos ⟨one_dvd _, hz⟩]
    have hsumG : ∑ r ∈ s.prodPrimes.divisors.filter (fun r => 1 ∣ r ∧ r ≤ z), s.selbergTerms r = G := by
      congr 1; ext r; simp
    rw [hsumG, ArithmeticFunction.moebius_apply_one, s.nu_mult.map_one]
    push_cast
    field_simp [hG_pos.ne']
  have hupper : BoundingSieve.IsUpperMoebius (BoundingSieve.lambdaSquared w) :=
    BoundingSieve.upperMoebius_lambdaSquared w hw1
  have hmain : s.mainSum (BoundingSieve.lambdaSquared w) = G⁻¹ := by
    rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq w]
    have hinner : ∀ l ∈ s.prodPrimes.divisors,
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * w d else 0) =
          if l ≤ z then (μ l : ℝ) * s.selbergTerms l / G else 0 := by
      intro l hl
      have hl_dvd : l ∣ s.prodPrimes := Nat.dvd_of_mem_divisors hl
      have hrewrite : (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * w d else 0) =
          G⁻¹ * ∑ d ∈ s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ≤ z),
            (μ d : ℝ) * ∑ r ∈ s.prodPrimes.divisors.filter (fun r => d ∣ r ∧ r ≤ z), s.selbergTerms r := by
        rw [Finset.mul_sum, ← Finset.sum_filter]
        have hsub : (s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ≤ z)) ⊆
            (s.prodPrimes.divisors.filter (fun d => l ∣ d)) := by
          intro d hd
          simp only [mem_filter] at hd ⊢
          exact ⟨hd.1, hd.2.1⟩
        rw [← Finset.sum_subset hsub]
        · refine Finset.sum_congr rfl fun d hd => ?_
          simp only [mem_filter, Nat.mem_divisors] at hd
          dsimp only [w]
          rw [if_pos ⟨hd.1.1, hd.2.2⟩]
          have hnu0 : s.nu d ≠ 0 := s.nu_ne_zero hd.1.1
          field_simp [hG_pos.ne', hnu0]
        · intro d hd hd_not
          simp only [mem_filter, Nat.mem_divisors] at hd hd_not
          have hgt : ¬ d ≤ z := fun hle => hd_not ⟨hd.1, hd.2, hle⟩
          dsimp only [w]
          rw [if_neg (fun h => hgt h.2), mul_zero]
      rw [hrewrite]
      split_ifs with hlz
      · -- l ≤ z: swap sum over d and r, then apply Mobius inversion
        have hswap : (∑ d ∈ s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ≤ z),
            (μ d : ℝ) * ∑ r ∈ s.prodPrimes.divisors.filter (fun r => d ∣ r ∧ r ≤ z), s.selbergTerms r) =
            ∑ r ∈ s.prodPrimes.divisors.filter (fun r => l ∣ r ∧ r ≤ z),
              s.selbergTerms r * ∑ d ∈ r.divisors.filter (fun d => l ∣ d), (μ d : ℝ) := by
          set T := s.prodPrimes.divisors.filter (fun r => l ∣ r ∧ r ≤ z)
          calc ∑ d ∈ T, (μ d : ℝ) *
                ∑ r ∈ s.prodPrimes.divisors.filter (fun r => d ∣ r ∧ r ≤ z), s.selbergTerms r
              = ∑ d ∈ T, ∑ r ∈ T, if d ∣ r then (μ d : ℝ) * s.selbergTerms r else 0 := by
                refine Finset.sum_congr rfl fun d hd => ?_
                rw [Finset.mul_sum, ← Finset.sum_filter]
                congr 1; ext r; simp only [T, mem_filter, Nat.mem_divisors]
                have hld : l ∣ d := (mem_filter.mp hd).2.1
                constructor
                · rintro ⟨⟨hrP, hP0⟩, hdr, hrz⟩; exact ⟨⟨⟨hrP, hP0⟩, hld.trans hdr, hrz⟩, hdr⟩
                · rintro ⟨⟨⟨hrP, hP0⟩, _, hrz⟩, hdr⟩; exact ⟨⟨hrP, hP0⟩, hdr, hrz⟩
            _ = ∑ r ∈ T, ∑ d ∈ T, if d ∣ r then (μ d : ℝ) * s.selbergTerms r else 0 := Finset.sum_comm
            _ = ∑ r ∈ T, s.selbergTerms r * ∑ d ∈ r.divisors.filter (fun d => l ∣ d), (μ d : ℝ) := by
                refine Finset.sum_congr rfl fun r hr => ?_
                rw [Finset.mul_sum, ← Finset.sum_filter]
                have hEq : T.filter (fun d => d ∣ r) = r.divisors.filter (fun d => l ∣ d) := by
                  ext d; simp only [T, mem_filter, Nat.mem_divisors]
                  have hrP : r ∣ s.prodPrimes := Nat.dvd_of_mem_divisors (mem_filter.mp hr).1
                  have hrz : r ≤ z := (mem_filter.mp hr).2.2
                  have hr0 : r ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hrP
                  constructor
                  · rintro ⟨⟨_, hld, _⟩, hdr⟩; exact ⟨⟨hdr, hr0⟩, hld⟩
                  · rintro ⟨⟨hdr, _⟩, hld⟩
                    exact ⟨⟨⟨hdr.trans hrP, s.prodPrimes_ne_zero⟩, hld,
                      (Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hdr).trans hrz⟩, hdr⟩
                rw [hEq]
                refine Finset.sum_congr rfl fun d _ => mul_comm _ _
        rw [hswap]
        have hmoeb : ∀ r ∈ s.prodPrimes.divisors.filter (fun r => l ∣ r ∧ r ≤ z),
            ∑ d ∈ r.divisors.filter (fun d => l ∣ d), (μ d : ℝ) = if r = l then (μ l : ℝ) else 0 := by
          intro r hr
          simp only [mem_filter, Nat.mem_divisors] at hr
          have hr_sq : Squarefree r := s.squarefree_of_dvd_prodPrimes hr.1.1
          have hr0 : r ≠ 0 := hr_sq.ne_zero
          have hl0 : l ≠ 0 := (s.squarefree_of_dvd_prodPrimes hl_dvd).ne_zero
          set m := r / l
          have hrm : r = l * m := (Nat.mul_div_cancel' hr.2.1).symm
          have hcop_lm : Nat.Coprime l m := by
            have h1 := hrm ▸ hr_sq
            exact Nat.coprime_of_squarefree_mul h1
          have hbij : r.divisors.filter (fun d => l ∣ d) = m.divisors.image (fun e => l * e) := by
            ext d
            simp only [mem_filter, Nat.mem_divisors, mem_image]
            constructor
            · rintro ⟨⟨hdr, _⟩, ⟨e, rfl⟩⟩
              refine ⟨e, ⟨?_, ?_⟩, rfl⟩
              · rw [hrm] at hdr; exact (mul_dvd_mul_iff_left hl0).mp hdr
              · intro hm0; rw [hm0, mul_zero] at hrm; exact hr0 hrm
            · rintro ⟨e, ⟨hem, _⟩, rfl⟩
              exact ⟨⟨by rw [hrm]; exact mul_dvd_mul_left l hem, hr0⟩, dvd_mul_right l e⟩
          rw [hbij, Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl0) hxy)]
          have hmult : ∀ e ∈ m.divisors, (μ (l * e) : ℝ) = (μ l : ℝ) * (μ e : ℝ) := by
            intro e he
            have hcop_le : Nat.Coprime l e := hcop_lm.coprime_dvd_right (Nat.dvd_of_mem_divisors he)
            have h1 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_le
            exact_mod_cast h1
          rw [Finset.sum_congr rfl hmult, ← Finset.mul_sum]
          have hsum_m : (∑ e ∈ m.divisors, (μ e : ℝ)) = if m = 1 then 1 else 0 := by
            have h1 : (μ * ζ : ArithmeticFunction ℝ) m = (1 : ArithmeticFunction ℝ) m := by
              rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
            rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h1
            simpa using h1
          rw [hsum_m]
          have hm_iff : m = 1 ↔ r = l := by
            constructor
            · intro h; rw [hrm, h, mul_one]
            · intro h
              have : l * m = l * 1 := by rw [← hrm, h, mul_one]
              exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hl0) this
          split_ifs with h1 h2 h2
          · ring
          · exact absurd (hm_iff.mp h1) h2
          · exact absurd (hm_iff.mpr h2) h1
          · ring
        rw [Finset.sum_congr rfl (fun r hr => by rw [hmoeb r hr])]
        rw [Finset.sum_eq_single l]
        · rw [if_pos rfl]; ring
        · intro r _ hrl; rw [if_neg hrl, mul_zero]
        · intro hl_not
          exfalso
          exact hl_not (mem_filter.mpr ⟨hl, dvd_rfl, hlz⟩)
      · -- l > z: filter is empty
        have hemp : s.prodPrimes.divisors.filter (fun d => l ∣ d ∧ d ≤ z) = ∅ := by
          rw [filter_eq_empty_iff]
          intro d hd ⟨hld, hdz⟩
          have hd0 : d ≠ 0 := (Nat.mem_divisors.mp hd).2 |> fun hP0 =>
            ne_zero_of_dvd_ne_zero hP0 (Nat.dvd_of_mem_divisors hd)
          have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hld
          omega
        rw [hemp, sum_empty, mul_zero]
    rw [Finset.sum_congr rfl (fun l hl => by rw [hinner l hl])]
    have hsimp : ∑ l ∈ s.prodPrimes.divisors,
        (s.selbergTerms l)⁻¹ * (if l ≤ z then (μ l : ℝ) * s.selbergTerms l / G else 0) ^ 2 =
        ∑ l ∈ s.prodPrimes.divisors.filter (· ≤ z), s.selbergTerms l * (G ^ 2)⁻¹ := by
      have hite : ∀ l ∈ s.prodPrimes.divisors,
          (s.selbergTerms l)⁻¹ * (if l ≤ z then (μ l : ℝ) * s.selbergTerms l / G else 0) ^ 2 =
          if l ≤ z then (s.selbergTerms l)⁻¹ * ((μ l : ℝ) * s.selbergTerms l / G) ^ 2 else 0 := by
        intro l _; split_ifs <;> simp
      rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hld := Nat.dvd_of_mem_divisors (mem_filter.mp hl).1
      have hmu2 : (μ l : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (s.squarefree_of_dvd_prodPrimes hld)
      have hgl : s.selbergTerms l ≠ 0 := (s.selbergTerms_pos hld).ne'
      calc (s.selbergTerms l)⁻¹ * ((μ l : ℝ) * s.selbergTerms l / G) ^ 2
          = (s.selbergTerms l)⁻¹ * ((μ l : ℝ) ^ 2 * (s.selbergTerms l) ^ 2 / G ^ 2) := by ring
        _ = (s.selbergTerms l)⁻¹ * (1 * (s.selbergTerms l) ^ 2 / G ^ 2) := by rw [hmu2]
        _ = s.selbergTerms l * (G ^ 2)⁻¹ := by field_simp [hgl, hG_pos.ne']
    rw [hsimp, ← Finset.sum_mul]
    change G * (G ^ 2)⁻¹ = G⁻¹
    field_simp [hG_pos.ne']
  have hw_abs : ∀ d, |w d| ≤ if d ∣ s.prodPrimes ∧ d ≤ z then 1 else 0 := by
    intro d
    dsimp only [w]
    split_ifs with hdz
    · obtain ⟨hdP, hdz_le⟩ := hdz
      have hnu_pos : 0 < s.nu d := s.nu_pos_of_dvd_prodPrimes hdP
      have hsum_nn : 0 ≤ ∑ r ∈ s.prodPrimes.divisors.filter (fun r => d ∣ r ∧ r ≤ z), s.selbergTerms r :=
        Finset.sum_nonneg fun r hr => (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hr).1)).le
      have hmu_abs : |(μ d : ℝ)| ≤ 1 := by
        have h1 : (μ d : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
            (s.squarefree_of_dvd_prodPrimes hdP)
        nlinarith [sq_abs (μ d : ℝ)]
      rw [abs_mul, abs_div, abs_of_pos (mul_pos hG_pos hnu_pos), abs_of_nonneg hsum_nn]
      have hstep1 : |(μ d : ℝ)| / (G * s.nu d) *
          (∑ r ∈ s.prodPrimes.divisors.filter (fun r => d ∣ r ∧ r ≤ z), s.selbergTerms r) ≤
          (1 / (G * s.nu d)) *
          (∑ r ∈ s.prodPrimes.divisors.filter (fun r => d ∣ r ∧ r ≤ z), s.selbergTerms r) := by
        apply mul_le_mul_of_nonneg_right _ hsum_nn
        exact div_le_div_of_nonneg_right hmu_abs (mul_pos hG_pos hnu_pos).le
      refine hstep1.trans ?_
      rw [one_div, mul_inv, mul_assoc, inv_mul_le_iff₀ hG_pos, mul_one]
      -- Show (s.nu d)⁻¹ * ∑_{d | r | P, r ≤ z} g(r) ≤ G
      have hd0 : d ≠ 0 := (s.squarefree_of_dvd_prodPrimes hdP).ne_zero
      set P' := s.prodPrimes / d
      have hPP' : s.prodPrimes = d * P' := (Nat.mul_div_cancel' hdP).symm
      have hcop_dP' : Nat.Coprime d P' := Nat.coprime_of_squarefree_mul (hPP' ▸ s.prodPrimes_squarefree)
      have hbij_r : s.prodPrimes.divisors.filter (fun r => d ∣ r ∧ r ≤ z) =
          (P'.divisors.filter (· ≤ z / d)).image (fun t => d * t) := by
        ext r
        simp only [mem_filter, Nat.mem_divisors, mem_image]
        constructor
        · rintro ⟨⟨hrP, hP0⟩, ⟨t, rfl⟩, hrz⟩
          refine ⟨t, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
          · rw [hPP'] at hrP; exact (mul_dvd_mul_iff_left hd0).mp hrP
          · intro h0; rw [h0, mul_zero] at hPP'; exact hP0 hPP'
          · exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd0)).mpr (by linarith)
        · rintro ⟨t, ⟨⟨htP', _⟩, htz⟩, rfl⟩
          refine ⟨⟨by rw [hPP']; exact mul_dvd_mul_left d htP', s.prodPrimes_ne_zero⟩,
            dvd_mul_right d t, ?_⟩
          have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd0)).mp htz
          linarith
      rw [hbij_r, Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) hxy)]
      have hmult_g : ∀ t ∈ P'.divisors.filter (· ≤ z / d),
          s.selbergTerms (d * t) = s.selbergTerms d * s.selbergTerms t := by
        intro t ht
        have htP' := Nat.dvd_of_mem_divisors (mem_filter.mp ht).1
        exact s.selbergTerms_isMultiplicative.map_mul_of_coprime (hcop_dP'.coprime_dvd_right htP')
      rw [Finset.sum_congr rfl hmult_g, ← Finset.mul_sum, ← mul_assoc, mul_comm (s.nu d)⁻¹,
        ← s.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
      rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hdP,
        Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_product']
      have hmult_ut : ∀ x ∈ d.divisors ×ˢ P'.divisors.filter (· ≤ z / d),
          s.selbergTerms x.1 * s.selbergTerms x.2 = s.selbergTerms (x.1 * x.2) := by
        intro ⟨u, t⟩ hxt
        rw [mem_product] at hxt
        have hu := Nat.dvd_of_mem_divisors hxt.1
        have ht := Nat.dvd_of_mem_divisors (mem_filter.mp hxt.2).1
        exact (s.selbergTerms_isMultiplicative.map_mul_of_coprime
          ((hcop_dP'.coprime_dvd_left hu).coprime_dvd_right ht)).symm
      rw [Finset.sum_congr rfl hmult_ut]
      have hinj_prod : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2)
          ((d.divisors ×ˢ P'.divisors.filter (· ≤ z / d) : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
        intro ⟨u1, t1⟩ h1 ⟨u2, t2⟩ h2 heq
        dsimp only at heq
        simp only [mem_coe, mem_product, mem_filter, Nat.mem_divisors] at h1 h2
        have hu1 := h1.1.1; have ht1 := h1.2.1.1
        have hu2 := h2.1.1; have ht2 := h2.2.1.1
        have hg1 : Nat.gcd (u1 * t1) d = u1 := by
          have hc : Nat.Coprime t1 d := (hcop_dP'.coprime_dvd_right ht1).symm
          rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel u1 hc, Nat.gcd_eq_left hu1]
        have hg2 : Nat.gcd (u2 * t2) d = u2 := by
          have hc : Nat.Coprime t2 d := (hcop_dP'.coprime_dvd_right ht2).symm
          rw [mul_comm, Nat.Coprime.gcd_mul_left_cancel u2 hc, Nat.gcd_eq_left hu2]
        have hu_eq : u1 = u2 := by rw [← hg1, ← hg2, heq]
        have hu1_pos : 0 < u1 := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hd0 hu1)
        have ht_eq : t1 = t2 := Nat.eq_of_mul_eq_mul_left hu1_pos (by rw [← hu_eq] at heq; exact heq)
        exact Prod.ext hu_eq ht_eq
      rw [← Finset.sum_image hinj_prod]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro l hl
        obtain ⟨⟨u, t⟩, hxt, rfl⟩ := mem_image.mp hl
        rw [mem_product] at hxt
        have hu := Nat.dvd_of_mem_divisors hxt.1
        have ht := Nat.dvd_of_mem_divisors (mem_filter.mp hxt.2).1
        have htz := (mem_filter.mp hxt.2).2
        simp only [mem_filter, Nat.mem_divisors]
        refine ⟨⟨by rw [hPP']; exact mul_dvd_mul hu ht, s.prodPrimes_ne_zero⟩, ?_⟩
        have hu_le : u ≤ d := Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hu
        have hdt_le : d * t ≤ z := by
          have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hd0)).mp htz
          linarith
        exact (Nat.mul_le_mul_right t hu_le).trans hdt_le
      · intro l hl _
        exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hl).1)).le
    · simp
  have herr : s.errSum (BoundingSieve.lambdaSquared w) ≤ (z : ℝ) ^ 2 := by
    rw [BoundingSieve.errSum]
    calc ∑ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d| * |s.rem d|
        ≤ ∑ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d| * 1 := by
          apply Finset.sum_le_sum fun d hd =>
            mul_le_mul_of_nonneg_left (hrem d hd) (abs_nonneg _)
      _ = ∑ d ∈ s.prodPrimes.divisors, |BoundingSieve.lambdaSquared w d| := by simp
      _ ≤ ∑ d ∈ s.prodPrimes.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
            if d = d1.lcm d2 then |w d1| * |w d2| else 0 := by
          refine Finset.sum_le_sum fun d _ => ?_
          dsimp only [BoundingSieve.lambdaSquared]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d1 _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d2 _ => ?_)
          split_ifs <;> simp [abs_mul]
      _ = ∑ d1 ∈ s.prodPrimes.divisors, ∑ d2 ∈ s.prodPrimes.divisors, |w d1| * |w d2| := by
          have hbig : ∀ d ∈ s.prodPrimes.divisors,
              (∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = d1.lcm d2 then |w d1| * |w d2| else 0) =
              (∑ d1 ∈ s.prodPrimes.divisors, ∑ d2 ∈ s.prodPrimes.divisors,
                if d = d1.lcm d2 then |w d1| * |w d2| else 0) := by
            intro d hd
            have hdP := Nat.dvd_of_mem_divisors hd
            have hd_sub : d.divisors ⊆ s.prodPrimes.divisors :=
              Nat.divisors_subset_of_dvd s.prodPrimes_ne_zero hdP
            rw [← Finset.sum_subset hd_sub]
            · refine Finset.sum_congr rfl fun d1 _ => ?_
              rw [← Finset.sum_subset hd_sub]
              intro d2 _ hd2_not
              rw [if_neg]
              intro heq
              exact hd2_not (Nat.mem_divisors.mpr ⟨heq ▸ Nat.dvd_lcm_right d1 d2,
                ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP⟩)
            · intro d1 _ hd1_not
              refine Finset.sum_eq_zero fun d2 _ => ?_
              rw [if_neg]
              intro heq
              exact hd1_not (Nat.mem_divisors.mpr ⟨heq ▸ Nat.dvd_lcm_left d1 d2,
                ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP⟩)
          rw [Finset.sum_congr rfl hbig, Finset.sum_comm]
          refine Finset.sum_congr rfl fun d1 hd1 => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d2 hd2 => ?_
          have hlcm : d1.lcm d2 ∈ s.prodPrimes.divisors :=
            Nat.mem_divisors.mpr ⟨Nat.lcm_dvd (Nat.dvd_of_mem_divisors hd1)
              (Nat.dvd_of_mem_divisors hd2), s.prodPrimes_ne_zero⟩
          rw [Finset.sum_ite_eq_of_mem' s.prodPrimes.divisors (d1.lcm d2) _ hlcm]
      _ = (∑ d ∈ s.prodPrimes.divisors, |w d|) ^ 2 := by
          rw [sq, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d1 _ => (Finset.mul_sum _ _ _).symm
      _ ≤ (z : ℝ) ^ 2 := by
          have hsum_w : ∑ d ∈ s.prodPrimes.divisors, |w d| ≤ z := by
            calc ∑ d ∈ s.prodPrimes.divisors, |w d|
                ≤ ∑ d ∈ s.prodPrimes.divisors, (if d ∣ s.prodPrimes ∧ d ≤ z then (1 : ℝ) else 0) :=
                  Finset.sum_le_sum fun d _ => hw_abs d
              _ = ((s.prodPrimes.divisors.filter (fun d => d ∣ s.prodPrimes ∧ d ≤ z)).card : ℝ) := by
                  simp [Finset.sum_boole]
              _ ≤ ((Icc 1 z).card : ℝ) := by
                  exact_mod_cast Finset.card_le_card fun d hd => by
                    simp only [mem_filter, Nat.mem_divisors] at hd
                    rw [mem_Icc]
                    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
                    exact ⟨Nat.pos_of_ne_zero hd0, hd.2.2⟩
              _ = (z : ℝ) := by simp
          have hnn : 0 ≤ ∑ d ∈ s.prodPrimes.divisors, |w d| :=
            Finset.sum_nonneg fun _ _ => abs_nonneg _
          nlinarith
  have hbound := s.siftedSum_le_mainSum_errSum_of_upperMoebius (BoundingSieve.lambdaSquared w) hupper
  rw [hmain] at hbound
  rw [div_eq_mul_inv]
  linarith

private lemma card_primes_ap_le_explicit {K z p a : ℕ} (hp : p.Prime) (_ha : 1 ≤ a)
    (hz1 : 1 ≤ z) (hzK : z ≤ K) :
    (((Ioc K (3 * K)).filter (fun q => q.Prime ∧ p ^ a ∣ q - 1)).card : ℝ) ≤
      4 * (K : ℝ) / ((p ^ a : ℝ) * Real.log (z + 1 : ℝ)) + (z : ℝ) ^ 2 := by
  set m := p ^ a
  have hm_pos : 0 < m := pow_pos hp.pos a
  set P := ∏ r ∈ z.primesLE.filter (· ≠ p), r
  have hP_sq : Squarefree P := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun x hx y hy hxy => ?_)
      (fun x hx => (Nat.prime_of_mem_primesLE (mem_filter.mp hx).1).squarefree)
    change IsRelPrime x y
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (Nat.prime_of_mem_primesLE (mem_filter.mp hx).1)
      (Nat.prime_of_mem_primesLE (mem_filter.mp hy).1)).mpr hxy
  have hP_cop_m : Nat.Coprime P m := by
    rw [Nat.coprime_comm]
    refine Nat.coprime_prod_right_iff.mpr fun r hr => ?_
    have hrp := Nat.prime_of_mem_primesLE (mem_filter.mp hr).1
    have hrne : r ≠ p := (mem_filter.mp hr).2
    exact ((Nat.coprime_primes hp hrp).mpr hrne.symm).pow_left a
  let s : BoundingSieve := {
    support := (Ioc K (3 * K)).filter (fun n => m ∣ n - 1)
    prodPrimes := P
    prodPrimes_squarefree := hP_sq
    weights := fun _ => 1
    weights_nonneg := fun _ => zero_le_one
    totalMass := (2 * K : ℝ) / (m : ℝ)
    nu := invId
    nu_mult := invId_isMultiplicative
    nu_pos_of_prime := fun q hq _ => by
      dsimp only [invId, ArithmeticFunction.coe_mk]
      rw [if_neg hq.ne_zero]
      have := hq.pos
      positivity
    nu_lt_one_of_prime := fun q hq _ => by
      dsimp only [invId, ArithmeticFunction.coe_mk]
      rw [if_neg hq.ne_zero]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.one_lt)
  }
  have hle_sifted : (((Ioc K (3 * K)).filter (fun q => q.Prime ∧ m ∣ q - 1)).card : ℝ) ≤
      s.siftedSum := by
    have hsub : (Ioc K (3 * K)).filter (fun q => q.Prime ∧ m ∣ q - 1) ⊆
        s.support.filter (fun q => Nat.Coprime P q) := by
      intro q hq
      simp only [mem_filter, mem_Ioc, s] at hq ⊢
      refine ⟨⟨hq.1, hq.2.2⟩, ?_⟩
      rw [Nat.coprime_comm]
      refine Nat.coprime_prod_right_iff.mpr fun r hr => ?_
      have hrp := Nat.prime_of_mem_primesLE (mem_filter.mp hr).1
      have hrz := Nat.le_of_mem_primesLE (mem_filter.mp hr).1
      have hr_lt_q : r < q := lt_of_le_of_lt (hrz.trans hzK) hq.1.1
      exact (Nat.coprime_primes hq.2.1 hrp).mpr hr_lt_q.ne'
    have hcard_le : ((Ioc K (3 * K)).filter (fun q => q.Prime ∧ m ∣ q - 1)).card ≤
        (s.support.filter (fun q => Nat.Coprime P q)).card := Finset.card_le_card hsub
    have hsifted_eq : s.siftedSum = ((s.support.filter (fun q => Nat.Coprime P q)).card : ℝ) := by
      simp [BoundingSieve.siftedSum, s, Finset.sum_boole]
    rw [hsifted_eq]
    exact_mod_cast hcard_le
  have hrem : ∀ d ∈ s.prodPrimes.divisors, |s.rem d| ≤ 1 := by
    intro d hd
    have hdP : d ∣ P := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hdP
    have hdm : Nat.Coprime d m := hP_cop_m.coprime_dvd_left hdP
    let c_sub := Nat.chineseRemainder hdm 0 1
    let c : ℕ := c_sub.val
    have hc_lt : c < d * m := Nat.chineseRemainder_lt_mul hdm 0 1 hd0 hm_pos.ne'
    have hmult_eq : s.multSum d = (((Ioc K (3 * K)).filter (fun n => n % (d * m) = c)).card : ℝ) := by
      dsimp only [BoundingSieve.multSum, s]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 2
      ext n
      simp only [mem_filter, mem_Ioc]
      constructor
      · rintro ⟨⟨hn, hmdvd⟩, hddvd⟩
        refine ⟨hn, ?_⟩
        have hn1 : n ≡ 1 [MOD m] := by
          have hn_ge1 : 1 ≤ n := by omega
          exact ((Nat.modEq_iff_dvd' hn_ge1).mpr hmdvd).symm
        have hnd : n ≡ 0 [MOD d] := Nat.modEq_zero_iff_dvd.mpr hddvd
        have hmod : n ≡ c [MOD d * m] := Nat.chineseRemainder_modEq_unique hdm hnd hn1
        exact Eq.trans hmod (Nat.mod_eq_of_lt hc_lt)
      · rintro ⟨hn, hmod⟩
        have hmod' : n ≡ c [MOD d * m] := by
          change n % (d * m) = c % (d * m)
          rw [hmod, Nat.mod_eq_of_lt hc_lt]
        have hnd : n ≡ 0 [MOD d] := (hmod'.of_dvd (dvd_mul_right d m)).trans c_sub.prop.1
        have hnm : n ≡ 1 [MOD m] := (hmod'.of_dvd (dvd_mul_left m d)).trans c_sub.prop.2
        have hn_ge1 : 1 ≤ n := by omega
        exact ⟨⟨hn, (Nat.modEq_iff_dvd' hn_ge1).mp hnm.symm⟩, Nat.modEq_zero_iff_dvd.mp hnd⟩
    dsimp only [BoundingSieve.rem]
    rw [hmult_eq]
    have hnu_d : s.nu d * s.totalMass = (2 * K : ℝ) / ((d * m : ℕ) : ℝ) := by
      dsimp only [s, invId, ArithmeticFunction.coe_mk]
      rw [if_neg hd0]
      push_cast
      field_simp [Nat.cast_ne_zero.mpr hd0, Nat.cast_ne_zero.mpr hm_pos.ne']
    rw [hnu_d]
    exact abs_card_Ioc_modEq_sub_le_one K (d * m) c (Nat.mul_pos (Nat.pos_of_ne_zero hd0) hm_pos) hc_lt
  have hsieve := selberg_siftedSum_le hz1 s (by dsimp only [s]; positivity) hrem
  have hG_ge := selberg_G_ge_log hp s rfl rfl
  have hlog_pos : 0 < Real.log (z + 1 : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < z + 1))
  have hdiv_le : s.totalMass / (∑ l ∈ s.prodPrimes.divisors.filter (· ≤ z), s.selbergTerms l) ≤
      4 * (K : ℝ) / ((m : ℝ) * Real.log (z + 1 : ℝ)) := by
    have hG_pos : 0 < (1 / 2 : ℝ) * Real.log (z + 1 : ℝ) := by positivity
    calc s.totalMass / (∑ l ∈ s.prodPrimes.divisors.filter (· ≤ z), s.selbergTerms l)
        ≤ s.totalMass / ((1 / 2 : ℝ) * Real.log (z + 1 : ℝ)) :=
          div_le_div_of_nonneg_left (by dsimp only [s]; positivity) hG_pos hG_ge
      _ = 4 * (K : ℝ) / ((m : ℝ) * Real.log (z + 1 : ℝ)) := by
          dsimp only [s]; field_simp [hlog_pos.ne', (Nat.cast_pos.mpr hm_pos).ne']; ring
  have hm_cast : ((m : ℕ) : ℝ) = (p : ℝ) ^ a := by dsimp only [m]; push_cast; rfl
  rw [← hm_cast]
  linarith

/- ### Section 4: Elementary Chebyshev and dyadic helper bounds -/

private lemma sum_primesLE_log_div_le (X : ℕ) (hX : 1 ≤ X) :
    ∑ p ∈ X.primesLE, Real.log (p : ℝ) / (p : ℝ) ≤ 4 * Real.log (X : ℝ) := by
  let M := Nat.log 2 X
  have hmaps : ∀ p ∈ X.primesLE, Nat.log 2 p ∈ Icc 1 M := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesLE hp
    have hpX := Nat.le_of_mem_primesLE hp
    rw [mem_Icc]
    refine ⟨?_, Nat.log_mono_right hpX⟩
    exact Nat.le_log_of_pow_le (by norm_num) (by simpa using hp_prime.two_le)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ j ∈ Icc 1 M,
      ∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j), Real.log (p : ℝ) / (p : ℝ) ≤
        4 * Real.log 2 := by
    intro j _
    calc ∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j), Real.log (p : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j), Real.log (p : ℝ) / ((2 ^ j : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
          have hlogj : Nat.log 2 p = j := (mem_filter.mp hp).2
          have h2j_le : 2 ^ j ≤ p := hlogj ▸ Nat.pow_log_le_self 2 hp_prime.ne_zero
          have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
          exact div_le_div_of_nonneg_left hlog_nn (by positivity) (by exact_mod_cast h2j_le)
      _ = (∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j), Real.log (p : ℝ)) / ((2 ^ j : ℕ) : ℝ) := by
          rw [← Finset.sum_div]
      _ ≤ (∑ p ∈ (2 ^ (j + 1)).primesLE, Real.log (Nat.cast p)) / ((2 ^ j : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            have hp_prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
            have hlogj : Nat.log 2 p = j := (mem_filter.mp hp).2
            rw [Nat.mem_primesLE]
            exact ⟨(hlogj ▸ Nat.lt_pow_succ_log_self (by norm_num) p).le, hp_prime⟩
          · intro p hp _
            exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
      _ = Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) / ((2 ^ j : ℕ) : ℝ) := by
          rw [Chebyshev.theta_eq_sum_primesLE_log]
      _ ≤ (Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ)) / ((2 ^ j : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) (by positivity)
      _ = 4 * Real.log 2 := by
          have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
          push_cast [pow_succ]
          rw [hlog4]
          field_simp [show (2 : ℝ) ^ j ≠ 0 by positivity]
          ring
  calc ∑ j ∈ Icc 1 M, ∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j), Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ _j ∈ Icc 1 M, (4 * Real.log 2) := Finset.sum_le_sum hblock
    _ = (M : ℝ) * (4 * Real.log 2) := by simp
    _ ≤ 4 * Real.log (X : ℝ) := by
        have h2M : ((2 ^ M : ℕ) : ℝ) ≤ (X : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 (by omega : X ≠ 0)
        have hlogM : (M : ℝ) * Real.log 2 ≤ Real.log (X : ℝ) := by
          have := Real.log_le_log (by positivity) h2M
          rwa [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at this
        linarith

private lemma sum_primesLE_log_div_mul_pred_le (X : ℕ) :
    ∑ p ∈ X.primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 4 * Real.log 4 := by
  let M := Nat.log 2 X
  have hmaps : ∀ p ∈ X.primesLE, Nat.log 2 p ∈ Icc 1 M := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesLE hp
    have hpX := Nat.le_of_mem_primesLE hp
    rw [mem_Icc]
    refine ⟨Nat.le_log_of_pow_le (by norm_num) (by simpa using hp_prime.two_le),
      Nat.log_mono_right hpX⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ j ∈ Icc 1 M,
      ∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j),
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        4 * Real.log 4 * ((2 : ℝ)⁻¹) ^ j := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hden_pos : (0 : ℝ) < (2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1) := by positivity
    calc ∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j),
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j),
            Real.log (p : ℝ) / ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
          have hlogj : Nat.log 2 p = j := (mem_filter.mp hp).2
          have h2j_le : 2 ^ j ≤ p := hlogj ▸ Nat.pow_log_le_self 2 hp_prime.ne_zero
          have h2j_leR : (2 : ℝ) ^ j ≤ (p : ℝ) := by exact_mod_cast h2j_le
          have h2jm1 : (2 : ℝ) ^ (j - 1) ≤ (p : ℝ) - 1 := by
            have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
              rw [← _root_.pow_succ', Nat.sub_add_cancel hj1]
            have h1 : 1 ≤ 2 ^ (j - 1) := Nat.one_le_pow _ _ (by norm_num)
            have h2 : 2 ^ (j - 1) ≤ p - 1 := by omega
            have h3 : 1 ≤ p := hp_prime.one_le
            have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by rw [Nat.cast_sub h3, Nat.cast_one]
            rw [← this]
            exact_mod_cast h2
          have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
          exact div_le_div_of_nonneg_left hlog_nn hden_pos
            (mul_le_mul h2j_leR h2jm1 (by positivity) (by positivity))
      _ = (∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j), Real.log (p : ℝ)) /
            ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) := by rw [← Finset.sum_div]
      _ ≤ (∑ p ∈ (2 ^ (j + 1)).primesLE, Real.log (Nat.cast p)) /
            ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) := by
          apply div_le_div_of_nonneg_right _ hden_pos.le
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro p hp
            have hp_prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
            have hlogj : Nat.log 2 p = j := (mem_filter.mp hp).2
            rw [Nat.mem_primesLE]
            exact ⟨(hlogj ▸ Nat.lt_pow_succ_log_self (by norm_num) p).le, hp_prime⟩
          · intro p hp _
            exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
      _ = Chebyshev.theta ((2 ^ (j + 1) : ℕ) : ℝ) / ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) := by
          rw [Chebyshev.theta_eq_sum_primesLE_log]
      _ ≤ (Real.log 4 * ((2 ^ (j + 1) : ℕ) : ℝ)) / ((2 : ℝ) ^ j * (2 : ℝ) ^ (j - 1)) := by
          apply div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) hden_pos.le
      _ = 4 * Real.log 4 * ((2 : ℝ)⁻¹) ^ j := by
          have hpow1 : (2 : ℝ) ^ j = 2 * (2 : ℝ) ^ (j - 1) := by
            rw [← _root_.pow_succ', Nat.sub_add_cancel hj1]
          push_cast [pow_succ]
          rw [inv_pow, hpow1]
          field_simp [show (2 : ℝ) ^ (j - 1) ≠ 0 by positivity]
          ring
  calc ∑ j ∈ Icc 1 M, ∑ p ∈ X.primesLE.filter (fun p => Nat.log 2 p = j),
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ j ∈ Icc 1 M, (4 * Real.log 4 * ((2 : ℝ)⁻¹) ^ j) := Finset.sum_le_sum hblock
    _ = 4 * Real.log 4 * ∑ j ∈ Icc 1 M, ((2 : ℝ)⁻¹) ^ j := by rw [← Finset.mul_sum]
    _ ≤ 4 * Real.log 4 * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsum_eq : ∑ j ∈ Icc 1 M, ((2 : ℝ)⁻¹) ^ j =
            (∑ j ∈ range (M + 1), ((2 : ℝ)⁻¹) ^ j) - 1 := by
          rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < M + 1)]
          have : Ico 1 (M + 1) = Icc 1 M := rfl
          rw [this]
          simp
        rw [hsum_eq, geom_sum_eq (by norm_num)]
        have : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ (M + 1) := by positivity
        rw [show (((2 : ℝ)⁻¹) ^ (M + 1) - 1) / ((2 : ℝ)⁻¹ - 1) =
            2 - 2 * ((2 : ℝ)⁻¹) ^ (M + 1) by ring]
        linarith
    _ = 4 * Real.log 4 := mul_one _

private lemma sum_Ioc_inv_sq_le (A B : ℕ) (hA : 1 ≤ A) :
    ∑ n ∈ Ioc A B, ((n : ℝ) ^ 2)⁻¹ ≤ (A : ℝ)⁻¹ := by
  induction B with
  | zero =>
    simp
  | succ B ih =>
    by_cases hAB : A ≤ B
    · rw [Finset.sum_Ioc_succ_top hAB]
      have htel : ∑ n ∈ Ioc A (B + 1), ((n : ℝ) ^ 2)⁻¹ ≤
          (A : ℝ)⁻¹ - ((B + 1 : ℕ) : ℝ)⁻¹ := by
        clear ih
        induction B, hAB using Nat.le_induction with
        | base =>
          have hI : Ioc A (A + 1) = {A + 1} := by
            ext x; simp only [mem_Ioc, mem_singleton]; omega
          rw [hI, sum_singleton]
          have hApos : (0 : ℝ) < A := by positivity
          have hA1pos : (0 : ℝ) < (A : ℝ) + 1 := by positivity
          push_cast
          rw [show (A : ℝ)⁻¹ - ((A : ℝ) + 1)⁻¹ = ((A : ℝ) * ((A : ℝ) + 1))⁻¹ by field_simp; ring]
          exact inv_anti₀ (by positivity) (by nlinarith)
        | succ m hm ihm =>
          rw [Finset.sum_Ioc_succ_top (by omega : A ≤ m + 1)]
          have hstep : (((m + 1 + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤
              ((m + 1 : ℕ) : ℝ)⁻¹ - ((m + 1 + 1 : ℕ) : ℝ)⁻¹ := by
            have h1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
            have h2 : (0 : ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
            have hdiff : ((m + 1 : ℕ) : ℝ)⁻¹ - ((m + 1 + 1 : ℕ) : ℝ)⁻¹ =
                (((m + 1 : ℕ) : ℝ) * ((m + 1 + 1 : ℕ) : ℝ))⁻¹ := by
              push_cast; field_simp; ring
            rw [hdiff]
            exact inv_anti₀ (by positivity) (by push_cast; nlinarith)
          linarith
      rw [← Finset.sum_Ioc_succ_top hAB]
      have hnn : (0 : ℝ) ≤ ((B + 1 : ℕ) : ℝ)⁻¹ := by positivity
      linarith
    · have hle : B + 1 ≤ A := by omega
      simp [Ioc_eq_empty_of_le hle]

private lemma sum_log_sub_one_decomp (K : ℕ) (hK : 2 ≤ K) :
    let P := (Ioc K (3 * K)).filter Nat.Prime
    let L := Nat.log 2 (3 * K)
    let N : ℕ → ℕ := fun m => (P.filter (fun q => m ∣ q - 1)).card
    ∑ q ∈ P, Real.log ((q - 1 : ℕ) : ℝ) =
      (∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) * (N p : ℝ)) +
      (∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) * ∑ a ∈ Icc 2 L, (N (p ^ a) : ℝ)) := by
  intro P L N
  have hlog_eq : ∀ q ∈ P,
      Real.log ((q - 1 : ℕ) : ℝ) =
        ∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) *
          (∑ a ∈ Icc 1 L, if p ^ a ∣ q - 1 then (1 : ℝ) else 0) := by
    intro q hq
    have hq_mem := mem_filter.mp hq
    have hq_Ioc := mem_Ioc.mp hq_mem.1
    have hq1_pos : 0 < q - 1 := by omega
    have hq1_le : q - 1 ≤ 3 * K := by omega
    have hfac_eq : ∀ p ∈ (3 * K).primesLE,
        ((q - 1).factorization p : ℝ) = ∑ a ∈ Icc 1 L, if p ^ a ∣ q - 1 then (1 : ℝ) else 0 := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primesLE hp
      have hcard : (q - 1).factorization p = ((Icc 1 L).filter (fun a => p ^ a ∣ q - 1)).card := by
        have hlt_pow : q - 1 < p ^ (L + 1) := by
          calc q - 1 ≤ 3 * K := hq1_le
            _ < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) (3 * K)
            _ ≤ p ^ (L + 1) := Nat.pow_le_pow_left hp_prime.two_le _
        have h1 := Nat.factorization_eq_card_pow_dvd_of_lt hp_prime hq1_pos hlt_pow
        have hIco : Ico 1 (L + 1) = Icc 1 L := rfl
        rw [hIco] at h1
        exact h1
      rw [hcard, Finset.sum_boole]
    calc Real.log ((q - 1 : ℕ) : ℝ)
        = Real.log (((∏ p ∈ (q - 1).primeFactors, p ^ ((q - 1).factorization p) : ℕ)) : ℝ) := by
          congr 2
          conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hq1_pos.ne']
          rw [Finsupp.prod, Nat.support_factorization]
      _ = ∑ p ∈ (q - 1).primeFactors, ((q - 1).factorization p : ℝ) * Real.log (p : ℝ) := by
          push_cast
          rw [Real.log_prod]
          · refine Finset.sum_congr rfl fun p _ => Real.log_pow _ _
          · intro p hp
            exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)
      _ = ∑ p ∈ (3 * K).primesLE, ((q - 1).factorization p : ℝ) * Real.log (p : ℝ) := by
          apply Finset.sum_subset
          · intro p hp
            rw [Nat.mem_primeFactors] at hp
            exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd hq1_pos hp.2.1).trans hq1_le, hp.1⟩
          · intro p _ hp_nmem
            have : (q - 1).factorization p = 0 := by
              by_contra h0
              exact hp_nmem (Nat.support_factorization (q - 1) ▸ Finsupp.mem_support_iff.mpr h0)
            simp [this]
      _ = ∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) *
            (∑ a ∈ Icc 1 L, if p ^ a ∣ q - 1 then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun p hp => by rw [mul_comm, hfac_eq p hp]
  rw [Finset.sum_congr rfl hlog_eq, Finset.sum_comm]
  have hL1 : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hsplit : ∀ p ∈ (3 * K).primesLE,
      (∑ q ∈ P, Real.log (p : ℝ) * ∑ a ∈ Icc 1 L, if p ^ a ∣ q - 1 then (1 : ℝ) else 0) =
        Real.log (p : ℝ) * (N p : ℝ) +
        Real.log (p : ℝ) * ∑ a ∈ Icc 2 L, (N (p ^ a) : ℝ) := by
    intro p _
    rw [← Finset.mul_sum, Finset.sum_comm, ← Finset.add_sum_Ioc_eq_sum_Icc hL1]
    have hIoc : Ioc 1 L = Icc 2 L := by ext a; simp [mem_Ioc, mem_Icc]; omega
    rw [hIoc, mul_add]
    congr 1
    · congr 1
      simp only [pow_one, Finset.sum_boole, N]
    · congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Finset.sum_boole, N]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]

private lemma sum_biUnion_le_of_nonneg {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (t : ι → Finset α) (f : α → ℝ)
    (hf : ∀ i ∈ s, ∀ a ∈ t i, 0 ≤ f a) :
    ∑ a ∈ s.biUnion t, f a ≤ ∑ i ∈ s, ∑ a ∈ t i, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [biUnion_insert, sum_insert hi]
    have h1 : ∑ a ∈ t i ∪ s.biUnion t, f a ≤ (∑ a ∈ t i, f a) + ∑ a ∈ s.biUnion t, f a := by
      rw [← Finset.sum_union_inter]
      have hnn : 0 ≤ ∑ a ∈ t i ∩ s.biUnion t, f a :=
        Finset.sum_nonneg fun a ha => hf i (mem_insert_self i s) a (mem_inter.mp ha).1
      linarith
    have h2 := ih (fun j hj => hf j (mem_insert_of_mem hj))
    linarith

/- ### Section 5: Main asymptotic contradiction and OMA.solution -/

private structure LargeK (K : ℕ) : Prop where
  hK1 : 100000 ≤ K
  hlog5 : Real.log (5 * (K : ℝ)) ≤ (K : ℝ) ^ ((1 : ℝ) / 1000)
  hlogK : (10000000 : ℝ) ≤ Real.log (K : ℝ)
  hR_big : (10000000 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 1000)

private lemma LargeK.Kpos {K : ℕ} (hK : LargeK K) : (0 : ℝ) < K := by
  have := hK.hK1; positivity

private lemma LargeK.R_pos {K : ℕ} (hK : LargeK K) : (0 : ℝ) < (K : ℝ) ^ ((1 : ℝ) / 1000) := by
  have := hK.Kpos; positivity

private lemma LargeK.logK_pos {K : ℕ} (hK : LargeK K) : 0 < Real.log (K : ℝ) := by
  linarith [hK.hlogK]

private lemma LargeK.log3_le {K : ℕ} (hK : LargeK K) :
    Real.log (3 * (K : ℝ)) ≤ (K : ℝ) ^ ((1 : ℝ) / 1000) := by
  have hKpos := hK.Kpos
  exact (Real.log_le_log (by positivity) (by linarith)).trans hK.hlog5

private lemma LargeK.logK_le {K : ℕ} (hK : LargeK K) :
    Real.log (K : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 1000) := by
  have hKpos := hK.Kpos
  exact (Real.log_le_log hKpos (by linarith)).trans hK.hlog5

private lemma LargeK.R_pow {K : ℕ} (hK : LargeK K) (a : ℝ) :
    (K : ℝ) ^ a = ((K : ℝ) ^ ((1 : ℝ) / 1000)) ^ (1000 * a) := by
  rw [← Real.rpow_mul hK.Kpos.le]
  congr 1; ring

private lemma LargeK.K_eq_R {K : ℕ} (hK : LargeK K) :
    (K : ℝ) = ((K : ℝ) ^ ((1 : ℝ) / 1000)) ^ (1000 : ℝ) := by
  simpa using hK.R_pow 1

private def PSet (K : ℕ) : Finset ℕ := (Ioc K (3 * K)).filter Nat.Prime

private def NCount (K m : ℕ) : ℕ := ((PSet K).filter (fun q => m ∣ q - 1)).card

private def IsGap (K Q : ℕ) : Prop := ∃ m ∈ Icc 2 400, K < Q ^ m ∧ Q ^ m ≤ 5 * K

private lemma sec5_lower_bound {K : ℕ} (hK : LargeK K) :
    0.65 * (K : ℝ) ≤ ∑ q ∈ PSet K, Real.log ((q - 1 : ℕ) : ℝ) := by
  have hK1 := hK.hK1
  have hKpos := hK.Kpos
  set R : ℝ := (K : ℝ) ^ ((1 : ℝ) / 1000)
  have hR_big : (10000000 : ℝ) ≤ R := hK.hR_big
  have hR_pos : 0 < R := hK.R_pos
  have hlog5 : Real.log (5 * (K : ℝ)) ≤ R := hK.hlog5
  have hlog3_le : Real.log (3 * (K : ℝ)) ≤ R := hK.log3_le
  have hR_pow : ∀ a : ℝ, (K : ℝ) ^ a = R ^ (1000 * a) := hK.R_pow
  have hK_eq_R : (K : ℝ) = R ^ (1000 : ℝ) := hK.K_eq_R
  have hP_eq : PSet K = (3 * K).primesLE \ K.primesLE := by
    ext q
    simp only [PSet, mem_filter, mem_Ioc, Finset.mem_sdiff, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩; exact ⟨⟨h2, hp⟩, fun h => by omega⟩
    · rintro ⟨⟨h2, hp⟩, hnot⟩
      exact ⟨⟨by by_contra h; exact hnot ⟨by omega, hp⟩, h2⟩, hp⟩
  have hsum_log_q : ∑ q ∈ PSet K, Real.log (q : ℝ) =
      Chebyshev.theta (3 * K : ℕ) - Chebyshev.theta (K : ℕ) := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, hP_eq]
    have hsub : K.primesLE ⊆ (3 * K).primesLE := Nat.primesLE_mono (by omega)
    rw [Finset.sum_sdiff_eq_sub hsub]
  have hdiff_le : ∑ q ∈ PSet K, (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ)) ≤ 2 := by
    have hterm : ∀ q ∈ PSet K, Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ) ≤ (K : ℝ)⁻¹ := by
      intro q hq
      have hqK : K < q := (mem_Ioc.mp (mem_filter.mp hq).1).1
      have hq1_pos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q - 1)
      have hq1 : 1 ≤ q := by omega
      have hq_cast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1, Nat.cast_one]
      rw [← Real.log_div (by positivity) hq1_pos.ne']
      have h1 : (q : ℝ) / ((q - 1 : ℕ) : ℝ) = 1 + (((q - 1 : ℕ) : ℝ))⁻¹ := by
        rw [hq_cast]; field_simp [show (q : ℝ) - 1 ≠ 0 by linarith [hq_cast ▸ hq1_pos]]; ring
      rw [h1]
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (((q - 1 : ℕ) : ℝ))⁻¹ by positivity)
      have h3 : (((q - 1 : ℕ) : ℝ))⁻¹ ≤ (K : ℝ)⁻¹ :=
        inv_anti₀ hKpos (by exact_mod_cast (by omega : K ≤ q - 1))
      linarith
    calc ∑ q ∈ PSet K, (Real.log (q : ℝ) - Real.log ((q - 1 : ℕ) : ℝ))
        ≤ ∑ _q ∈ PSet K, (K : ℝ)⁻¹ := Finset.sum_le_sum hterm
      _ = ((PSet K).card : ℝ) * (K : ℝ)⁻¹ := by simp
      _ ≤ (2 * K : ℝ) * (K : ℝ)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (PSet K).card ≤ (Ioc K (3 * K)).card := Finset.card_filter_le _ _
          have hcard : (Ioc K (3 * K)).card = 2 * K := by simp; omega
          exact_mod_cast hcard ▸ this
      _ = 2 := by field_simp [hKpos.ne']
  have htheta3 := Chebyshev.theta_ge (3 * K)
  have htheta1 := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ (K : ℝ) by positivity)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow, Nat.cast_ofNat]
  have hlog2 : 0.693 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hsub_sum : ∑ q ∈ PSet K, Real.log (q : ℝ) - ∑ q ∈ PSet K, Real.log ((q - 1 : ℕ) : ℝ) ≤ 2 := by
    rwa [← Finset.sum_sub_distrib]
  have hsqrt_le : 2 * Real.sqrt ((3 * K : ℕ) : ℝ) * Real.log ((3 * K : ℕ) : ℝ) ≤ 0.01 * (K : ℝ) := by
    have hsq : Real.sqrt ((3 * K : ℕ) : ℝ) ≤ 2 * (K : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (K : ℝ)]
      have : Real.sqrt 3 ≤ 2 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith [show (0 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 2) by positivity]
    have hlog3' : Real.log ((3 * K : ℕ) : ℝ) ≤ R := by push_cast; exact hlog3_le
    have hKR : (K : ℝ) ^ ((1 : ℝ) / 2) * R ≤ (K : ℝ) / R := by
      rw [le_div_iff₀ hR_pos, mul_assoc, ← sq, hR_pow (1 / 2), hK_eq_R]
      rw [show (R ^ (1000 * ((1 : ℝ) / 2)) * R ^ (2 : ℕ)) = R ^ (502 : ℝ) by
        rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR_pos]; norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h1 : 2 * Real.sqrt ((3 * K : ℕ) : ℝ) * Real.log ((3 * K : ℕ) : ℝ) ≤
        4 * ((K : ℝ) ^ ((1 : ℝ) / 2) * R) := by
      have hln : 0 ≤ Real.log ((3 * K : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 3 * K))
      nlinarith [Real.sqrt_nonneg ((3 * K : ℕ) : ℝ)]
    have h2 : 4 * ((K : ℝ) / R) ≤ 0.01 * (K : ℝ) := by
      rw [← mul_div_assoc, div_le_iff₀ hR_pos]
      nlinarith
    linarith
  have hlog3p1 : Real.log ((3 * K + 1 : ℕ) : ℝ) ≤ 0.01 * (K : ℝ) := by
    have h1 : Real.log ((3 * K + 1 : ℕ) : ℝ) ≤ R := by
      refine (Real.log_le_log (by positivity) ?_).trans hlog5
      push_cast; linarith [show (1 : ℝ) ≤ K by exact_mod_cast (by omega : 1 ≤ K)]
    have h2 : R ≤ (K : ℝ) / R := by
      rw [le_div_iff₀ hR_pos, ← sq, hK_eq_R, ← Real.rpow_natCast R 2]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have h3 : (K : ℝ) / R ≤ 0.01 * (K : ℝ) := by
      rw [div_le_iff₀ hR_pos]; nlinarith
    linarith
  have hK200 : (200 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 200 ≤ K)
  have hKlog2 : 0.693 * (K : ℝ) ≤ (K : ℝ) * Real.log 2 := by nlinarith
  push_cast at htheta3 hsum_log_q hsqrt_le hlog3p1
  rw [hlog4] at htheta1
  linarith [hsum_log_q, htheta3, htheta1, hsub_sum, hsqrt_le, hlog3p1, hK200, hKlog2]

private lemma sec5_sieve_bound {K : ℕ} (hK : LargeK K) {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hpa_le : ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)) :
    (NCount K (p ^ a) : ℝ) ≤ 33 * (K : ℝ) / (((p ^ a : ℕ) : ℝ) * Real.log (K : ℝ)) := by
  have hK1 := hK.hK1
  have hKpos := hK.Kpos
  set R : ℝ := (K : ℝ) ^ ((1 : ℝ) / 1000)
  have hR_big : (10000000 : ℝ) ≤ R := hK.hR_big
  have hR_pos : 0 < R := hK.R_pos
  have hlogK_pos : 0 < Real.log (K : ℝ) := hK.logK_pos
  have hlogK_le : Real.log (K : ℝ) ≤ R := hK.logK_le
  have hR_pow : ∀ x : ℝ, (K : ℝ) ^ x = R ^ (1000 * x) := hK.R_pow
  have hK_eq_R : (K : ℝ) = R ^ (1000 : ℝ) := hK.K_eq_R
  set z : ℕ := Nat.floor ((K : ℝ) ^ ((1 : ℝ) / 8))
  have hz_gt : (K : ℝ) ^ ((1 : ℝ) / 8) < (z : ℝ) + 1 := Nat.lt_floor_add_one _
  have hz_le : (z : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 8) := Nat.floor_le (by positivity)
  have hz1 : 1 ≤ z := by
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ K)) (by norm_num)
  have hzK : z ≤ K := by
    have : (z : ℝ) ≤ (K : ℝ) := hz_le.trans (by
      rw [hR_pow (1 / 8), hK_eq_R]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
    exact_mod_cast this
  have hlogz : (1 / 8 : ℝ) * Real.log (K : ℝ) ≤ Real.log ((z : ℝ) + 1) := by
    have h1 := Real.log_le_log (by positivity) hz_gt.le
    rwa [Real.log_rpow hKpos] at h1
  have hbt := card_primes_ap_le_explicit hp ha hz1 hzK
  have hpa_pos : (0 : ℝ) < ((p ^ a : ℕ) : ℝ) := Nat.cast_pos.mpr (pow_pos hp.pos a)
  have hterm1 : 4 * (K : ℝ) / (((p ^ a : ℕ) : ℝ) * Real.log ((z : ℝ) + 1)) ≤
      32 * (K : ℝ) / (((p ^ a : ℕ) : ℝ) * Real.log (K : ℝ)) := by
    have hden : (0 : ℝ) < ((p ^ a : ℕ) : ℝ) * ((1 / 8 : ℝ) * Real.log (K : ℝ)) := by positivity
    calc 4 * (K : ℝ) / (((p ^ a : ℕ) : ℝ) * Real.log ((z : ℝ) + 1))
        ≤ 4 * (K : ℝ) / (((p ^ a : ℕ) : ℝ) * ((1 / 8 : ℝ) * Real.log (K : ℝ))) :=
          div_le_div_of_nonneg_left (by positivity) hden
            (mul_le_mul_of_nonneg_left hlogz hpa_pos.le)
      _ = 32 * (K : ℝ) / (((p ^ a : ℕ) : ℝ) * Real.log (K : ℝ)) := by
          field_simp [hpa_pos.ne', hlogK_pos.ne']; ring
  have hterm2 : (z : ℝ) ^ 2 ≤ (K : ℝ) / (((p ^ a : ℕ) : ℝ) * Real.log (K : ℝ)) := by
    rw [le_div_iff₀ (mul_pos hpa_pos hlogK_pos)]
    have hz2 : (z : ℝ) ^ 2 ≤ (K : ℝ) ^ ((1 : ℝ) / 4) := by
      calc (z : ℝ) ^ 2 ≤ ((K : ℝ) ^ ((1 : ℝ) / 8)) ^ 2 := by nlinarith
        _ = (K : ℝ) ^ ((1 : ℝ) / 4) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le]; norm_num
    calc (z : ℝ) ^ 2 * (((p ^ a : ℕ) : ℝ) * Real.log (K : ℝ))
        ≤ (K : ℝ) ^ ((1 : ℝ) / 4) * ((K : ℝ) ^ ((3 : ℝ) / 5) * R) := by
          apply mul_le_mul hz2 (mul_le_mul hpa_le hlogK_le hlogK_pos.le (by positivity))
            (by positivity) (by positivity)
      _ = R ^ (851 : ℝ) := by
          rw [hR_pow (1 / 4), hR_pow (3 / 5)]
          rw [show R ^ (1000 * ((1 : ℝ) / 4)) * (R ^ (1000 * ((3 : ℝ) / 5)) * R) =
              R ^ (250 : ℝ) * R ^ (600 : ℝ) * R ^ (1 : ℝ) by rw [Real.rpow_one]; norm_num; ring]
          rw [← Real.rpow_add hR_pos, ← Real.rpow_add hR_pos]; norm_num
      _ ≤ R ^ (1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (K : ℝ) := hK_eq_R.symm
  have hpa_cast : ((p ^ a : ℕ) : ℝ) = (p : ℝ) ^ a := by push_cast; rfl
  rw [hpa_cast] at hterm1 hterm2 ⊢
  dsimp only [NCount, PSet]
  rw [Finset.filter_filter]
  have hadd : 32 * (K : ℝ) / ((p : ℝ) ^ a * Real.log (K : ℝ)) +
      (K : ℝ) / ((p : ℝ) ^ a * Real.log (K : ℝ)) =
      33 * (K : ℝ) / ((p : ℝ) ^ a * Real.log (K : ℝ)) := by ring
  linarith [hbt, hterm1, hterm2, hadd]

private lemma sec5_ha2_case1 {K : ℕ} (hK : LargeK K) :
    let L := Nat.log 2 (3 * K)
    ∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) *
      (∑ a ∈ (Icc 2 L).filter (fun a => ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)), (NCount K (p ^ a) : ℝ)) ≤
      0.01 * (K : ℝ) := by
  intro L
  have hKpos := hK.Kpos
  have hlogK := hK.hlogK
  have hlogK_pos := hK.logK_pos
  have hterm_p : ∀ p ∈ (3 * K).primesLE,
      Real.log (p : ℝ) *
        (∑ a ∈ (Icc 2 L).filter (fun a => ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)), (NCount K (p ^ a) : ℝ)) ≤
        33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p hp_mem
    have hp := Nat.prime_of_mem_primesLE hp_mem
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have hsum_a : ∑ a ∈ (Icc 2 L).filter (fun a => ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)),
        (NCount K (p ^ a) : ℝ) ≤ 33 * (K : ℝ) / Real.log (K : ℝ) * (((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
      calc ∑ a ∈ (Icc 2 L).filter (fun a => ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)), (NCount K (p ^ a) : ℝ)
          ≤ ∑ a ∈ (Icc 2 L).filter (fun a => ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)),
              33 * (K : ℝ) / (((p ^ a : ℕ) : ℝ) * Real.log (K : ℝ)) := by
            refine Finset.sum_le_sum fun a ha => ?_
            have ha2 : 2 ≤ a := (mem_Icc.mp (mem_filter.mp ha).1).1
            exact sec5_sieve_bound hK hp (by omega) (mem_filter.mp ha).2
        _ ≤ ∑ a ∈ Icc 2 L, 33 * (K : ℝ) / (((p ^ a : ℕ) : ℝ) * Real.log (K : ℝ)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
        _ = 33 * (K : ℝ) / Real.log (K : ℝ) * ∑ a ∈ Icc 2 L, ((p : ℝ)⁻¹) ^ a := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            push_cast; rw [inv_pow]; ring
        _ ≤ 33 * (K : ℝ) / Real.log (K : ℝ) * ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have hshift : ∑ a ∈ Icc 2 L, ((p : ℝ)⁻¹) ^ a =
                ((p : ℝ)⁻¹) ^ 2 * ∑ j ∈ range (L - 1), ((p : ℝ)⁻¹) ^ j := by
              rw [Finset.mul_sum]
              by_cases hL2 : 2 ≤ L
              · have hbij : Icc 2 L = (range (L - 1)).image (fun j => j + 2) := by
                  ext x; simp only [mem_Icc, mem_image, mem_range]
                  constructor
                  · intro ⟨h1, h2⟩; exact ⟨x - 2, by omega, by omega⟩
                  · rintro ⟨j, hj, rfl⟩; omega
                rw [hbij, Finset.sum_image (fun x _ y _ hxy => by omega)]
                refine Finset.sum_congr rfl fun j _ => by rw [pow_add, mul_comm]
              · have h1 : Icc 2 L = ∅ := Icc_eq_empty (by omega)
                have h2 : L - 1 = 0 := by omega
                simp [h1, h2]
            rw [hshift]
            have hp_lt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
            have hgeom : ∑ j ∈ range (L - 1), ((p : ℝ)⁻¹) ^ j ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
              have hpow_nn : (0 : ℝ) ≤ (p : ℝ)⁻¹ ^ (L - 1) := by positivity
              rw [geom_sum_eq hp_lt.ne, ← neg_div_neg_eq, neg_sub, neg_sub,
                div_le_iff₀ (by linarith : (0 : ℝ) < 1 - (p : ℝ)⁻¹)]
              have hinv : (1 - (p : ℝ)⁻¹)⁻¹ * (1 - (p : ℝ)⁻¹) = 1 :=
                inv_mul_cancel₀ (by linarith)
              linarith
            have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
            have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
              have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
              linarith
            have heq : ((p : ℝ)⁻¹) ^ 2 * (1 - (p : ℝ)⁻¹)⁻¹ = ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
              field_simp [hp_pos.ne', hp1_pos.ne']
            rw [← heq]
            exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    calc Real.log (p : ℝ) * _
        ≤ Real.log (p : ℝ) * (33 * (K : ℝ) / Real.log (K : ℝ) * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) :=
          mul_le_mul_of_nonneg_left hsum_a hlogp_nn
      _ = 33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
          ring
  calc ∑ p ∈ (3 * K).primesLE, _
      ≤ ∑ p ∈ (3 * K).primesLE,
          33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) :=
        Finset.sum_le_sum hterm_p
    _ = 33 * (K : ℝ) / Real.log (K : ℝ) *
          ∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        rw [← Finset.mul_sum]
    _ ≤ 33 * (K : ℝ) / Real.log (K : ℝ) * (4 * Real.log 4) :=
        mul_le_mul_of_nonneg_left (sum_primesLE_log_div_mul_pred_le (3 * K)) (by positivity)
    _ ≤ 0.01 * (K : ℝ) := by
        have hlog4_lt : Real.log (4 : ℝ) < 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow, Nat.cast_ofNat]
          linarith [Real.log_two_lt_d9]
        rw [show 33 * (K : ℝ) / Real.log (K : ℝ) * (4 * Real.log 4) =
            (33 * (K : ℝ) * (4 * Real.log 4)) / Real.log (K : ℝ) by ring, div_le_iff₀ hlogK_pos]
        nlinarith

private lemma sec5_ha2_case2 {K : ℕ} (hK : LargeK K) :
    let L := Nat.log 2 (3 * K)
    ∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) *
      (∑ a ∈ (Icc 2 L).filter (fun a => ¬ ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)), (NCount K (p ^ a) : ℝ)) ≤
      0.01 * (K : ℝ) := by
  intro L
  have hK1 := hK.hK1
  have hKpos := hK.Kpos
  set R : ℝ := (K : ℝ) ^ ((1 : ℝ) / 1000)
  have hR_big : (10000000 : ℝ) ≤ R := hK.hR_big
  have hR_pos : 0 < R := hK.R_pos
  have hlog3_le : Real.log (3 * (K : ℝ)) ≤ R := hK.log3_le
  have hR_pow : ∀ x : ℝ, (K : ℝ) ^ x = R ^ (1000 * x) := hK.R_pow
  have hK_eq_R : (K : ℝ) = R ^ (1000 : ℝ) := hK.K_eq_R
  have htriv : ∀ m : ℕ, 0 < m → (NCount K m : ℝ) ≤ (2 * K : ℝ) / (m : ℝ) + 1 := by
    intro m hm
    have hsub : (PSet K).filter (fun q => m ∣ q - 1) ⊆
        (Ioc K (3 * K)).filter (fun n => n % m = 1 % m) := by
      intro q hq
      simp only [PSet, mem_filter, mem_Ioc] at hq ⊢
      refine ⟨hq.1.1, ?_⟩
      have hq1 : 1 ≤ q := by omega
      exact ((Nat.modEq_iff_dvd' hq1).mpr hq.2).symm
    have h1 : (NCount K m : ℝ) ≤ (((Ioc K (3 * K)).filter (fun n => n % m = 1 % m)).card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hsub
    have h2 := (abs_le.mp (abs_card_Ioc_modEq_sub_le_one K m (1 % m) hm (Nat.mod_lt 1 hm))).2
    linarith
  have hzero_big : ∀ p ∈ (3 * K).primesLE, 3 * K < p ^ 2 →
      ∑ a ∈ (Icc 2 L).filter (fun a => ¬ ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)), (NCount K (p ^ a) : ℝ) = 0 := by
    intro p hp hp2
    refine Finset.sum_eq_zero fun a ha => ?_
    have ha2 : 2 ≤ a := (mem_Icc.mp (mem_filter.mp ha).1).1
    have hp_pos := (Nat.prime_of_mem_primesLE hp).pos
    have hpa_gt : 3 * K < p ^ a := lt_of_lt_of_le hp2 (Nat.pow_le_pow_right hp_pos ha2)
    have hemp : (PSet K).filter (fun q => p ^ a ∣ q - 1) = ∅ := by
      rw [filter_eq_empty_iff]
      intro q hq hdvd
      have hq_Ioc := mem_Ioc.mp (mem_filter.mp hq).1
      have hle := Nat.le_of_dvd (by omega : 0 < q - 1) hdvd
      omega
    simp [NCount, hemp]
  have hsub_sqrt : (3 * K).primesLE.filter (fun p => p ^ 2 ≤ 3 * K) ⊆ Icc 1 (Nat.sqrt (3 * K)) := by
    intro p hp
    simp only [mem_filter, Nat.mem_primesLE] at hp
    rw [mem_Icc]
    exact ⟨hp.1.2.one_le, Nat.le_sqrt.mpr (by simpa [sq] using hp.2)⟩
  have hterm_le : ∀ p ∈ (3 * K).primesLE.filter (fun p => p ^ 2 ≤ 3 * K),
      Real.log (p : ℝ) *
        (∑ a ∈ (Icc 2 L).filter (fun a => ¬ ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)), (NCount K (p ^ a) : ℝ)) ≤
        R * ((L : ℝ) * (2 * (K : ℝ) ^ ((2 : ℝ) / 5) + 1)) := by
    intro p hp
    have hp_mem := (mem_filter.mp hp).1
    have hp_prime := Nat.prime_of_mem_primesLE hp_mem
    have hp_le := Nat.le_of_mem_primesLE hp_mem
    have hlogp : Real.log (p : ℝ) ≤ R :=
      (Real.log_le_log (Nat.cast_pos.mpr hp_prime.pos) (by exact_mod_cast hp_le)).trans hlog3_le
    set Fa := (Icc 2 L).filter (fun a => ¬ ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5))
    have hsum_a : ∑ a ∈ Fa, (NCount K (p ^ a) : ℝ) ≤ (L : ℝ) * (2 * (K : ℝ) ^ ((2 : ℝ) / 5) + 1) := by
      calc ∑ a ∈ Fa, (NCount K (p ^ a) : ℝ)
          ≤ ∑ _a ∈ Fa, (2 * (K : ℝ) ^ ((2 : ℝ) / 5) + 1) := by
            refine Finset.sum_le_sum fun a ha => ?_
            have hgt : (K : ℝ) ^ ((3 : ℝ) / 5) < ((p ^ a : ℕ) : ℝ) := not_le.mp (mem_filter.mp ha).2
            have h1 := htriv (p ^ a) (pow_pos hp_prime.pos a)
            have h2 : (2 * K : ℝ) / ((p ^ a : ℕ) : ℝ) ≤ (2 * K : ℝ) / (K : ℝ) ^ ((3 : ℝ) / 5) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hgt.le
            have h3 : (2 * K : ℝ) / (K : ℝ) ^ ((3 : ℝ) / 5) = 2 * (K : ℝ) ^ ((2 : ℝ) / 5) := by
              rw [mul_div_assoc, show (K : ℝ) / (K : ℝ) ^ ((3 : ℝ) / 5) = (K : ℝ) ^ ((2 : ℝ) / 5) by
                rw [div_eq_iff (by positivity), ← Real.rpow_add hKpos]; norm_num]
            linarith
        _ = (Fa.card : ℝ) * (2 * (K : ℝ) ^ ((2 : ℝ) / 5) + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (L : ℝ) * (2 * (K : ℝ) ^ ((2 : ℝ) / 5) + 1) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have hc : Fa.card ≤ (Icc 2 L).card := Finset.card_filter_le _ _
            have hc2 : (Icc 2 L).card ≤ L := by rw [Nat.card_Icc]; omega
            exact_mod_cast hc.trans hc2
    exact mul_le_mul hlogp hsum_a (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  have hL_le : (L : ℝ) ≤ 2 * R := by
    have h2L : ((2 ^ L : ℕ) : ℝ) ≤ (3 * K : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : 3 * K ≠ 0)
    have h1 := Real.log_le_log (by positivity) h2L
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at h1
    have hlog2 : (0.5 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have hsqrt_le : (Nat.sqrt (3 * K) : ℝ) ≤ 2 * (K : ℝ) ^ ((1 : ℝ) / 2) := by
    have hsq : ((Nat.sqrt (3 * K) : ℝ)) ^ 2 ≤ 3 * (K : ℝ) := by
      rw [sq]; exact_mod_cast Nat.sqrt_le (3 * K)
    have h1 : (Nat.sqrt (3 * K) : ℝ) ≤ Real.sqrt (3 * (K : ℝ)) := by
      rw [Real.le_sqrt (by positivity) (by positivity)]; exact hsq
    have h2 : Real.sqrt (3 * (K : ℝ)) ≤ 2 * (K : ℝ) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (K : ℝ)]
      have : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
      nlinarith [show (0 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 2) by positivity]
    linarith
  calc ∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) * _
      = ∑ p ∈ (3 * K).primesLE.filter (fun p => p ^ 2 ≤ 3 * K), Real.log (p : ℝ) * _ := by
        symm
        apply Finset.sum_subset (filter_subset _ _)
        intro p hp hp_not
        have hgt : 3 * K < p ^ 2 := by
          have hnotle : ¬ p ^ 2 ≤ 3 * K := fun h => hp_not (mem_filter.mpr ⟨hp, h⟩)
          omega
        rw [hzero_big p hp hgt, mul_zero]
    _ ≤ ∑ _p ∈ (3 * K).primesLE.filter (fun p => p ^ 2 ≤ 3 * K),
          R * ((L : ℝ) * (2 * (K : ℝ) ^ ((2 : ℝ) / 5) + 1)) :=
        Finset.sum_le_sum hterm_le
    _ = (((3 * K).primesLE.filter (fun p => p ^ 2 ≤ 3 * K)).card : ℝ) *
          (R * ((L : ℝ) * (2 * (K : ℝ) ^ ((2 : ℝ) / 5) + 1))) := by simp
    _ ≤ (Nat.sqrt (3 * K) : ℝ) * (R * ((2 * R) * (3 * (K : ℝ) ^ ((2 : ℝ) / 5)))) := by
        have hcard : (((3 * K).primesLE.filter (fun p => p ^ 2 ≤ 3 * K)).card : ℝ) ≤
            (Nat.sqrt (3 * K) : ℝ) := by
          have h1 := Finset.card_le_card hsub_sqrt
          simp at h1
          exact_mod_cast h1
        have hK25 : (1 : ℝ) ≤ (K : ℝ) ^ ((2 : ℝ) / 5) :=
          Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ K)) (by norm_num)
        apply mul_le_mul hcard
        · apply mul_le_mul_of_nonneg_left _ hR_pos.le
          exact mul_le_mul hL_le (by linarith) (by positivity) (by positivity)
        · positivity
        · positivity
    _ ≤ (2 * (K : ℝ) ^ ((1 : ℝ) / 2)) * (6 * R ^ 2 * (K : ℝ) ^ ((2 : ℝ) / 5)) := by
        have : R * (2 * R * (3 * (K : ℝ) ^ ((2 : ℝ) / 5))) = 6 * R ^ 2 * (K : ℝ) ^ ((2 : ℝ) / 5) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hsqrt_le (by positivity)
    _ = 12 * R ^ (902 : ℝ) := by
        rw [hR_pow (1 / 2), hR_pow (2 / 5)]
        have h1 : (2 * R ^ (1000 * ((1 : ℝ) / 2))) * (6 * R ^ (2 : ℕ) * R ^ (1000 * ((2 : ℝ) / 5))) =
            12 * (R ^ (500 : ℝ) * R ^ (2 : ℝ) * R ^ (400 : ℝ)) := by
          rw [← Real.rpow_natCast R 2]; norm_num; ring
        rw [h1, ← Real.rpow_add hR_pos, ← Real.rpow_add hR_pos]; norm_num
    _ ≤ 0.01 * (K : ℝ) := by
        have hpow : R ^ (902 : ℝ) * R = R ^ (903 : ℝ) := by
          calc R ^ (902 : ℝ) * R = R ^ (902 : ℝ) * R ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = R ^ (903 : ℝ) := by rw [← Real.rpow_add hR_pos]; norm_num
        have hle : R ^ (903 : ℝ) ≤ (K : ℝ) := by
          rw [hK_eq_R]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        have hdiv : R ^ (902 : ℝ) ≤ (K : ℝ) / R := by
          rw [le_div_iff₀ hR_pos, hpow]; exact hle
        have h12 : 12 * ((K : ℝ) / R) ≤ 0.01 * (K : ℝ) := by
          rw [← mul_div_assoc, div_le_iff₀ hR_pos]; nlinarith
        linarith

private lemma sec5_ha2_bound {K : ℕ} (hK : LargeK K) :
    ∑ p ∈ (3 * K).primesLE, Real.log (p : ℝ) * ∑ a ∈ Icc 2 (Nat.log 2 (3 * K)), (NCount K (p ^ a) : ℝ) ≤
      0.02 * (K : ℝ) := by
  set L := Nat.log 2 (3 * K)
  have hsplit_a : ∀ p ∈ (3 * K).primesLE,
      ∑ a ∈ Icc 2 L, (NCount K (p ^ a) : ℝ) =
        (∑ a ∈ (Icc 2 L).filter (fun a => ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)), (NCount K (p ^ a) : ℝ)) +
        (∑ a ∈ (Icc 2 L).filter (fun a => ¬ ((p ^ a : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5)), (NCount K (p ^ a) : ℝ)) := by
    intro p _
    exact (Finset.sum_filter_add_sum_filter_not (Icc 2 L) _ _).symm
  rw [Finset.sum_congr rfl (fun p hp => by rw [hsplit_a p hp, mul_add]), Finset.sum_add_distrib]
  linarith [sec5_ha2_case1 hK, sec5_ha2_case2 hK]

private lemma sec5_small_bound {K : ℕ} (hK : LargeK K) :
    let X_small : ℕ := Nat.floor ((K : ℝ) ^ ((1 : ℝ) / 400))
    ∑ p ∈ (3 * K).primesLE.filter (fun p => p ≤ X_small), Real.log (p : ℝ) * (NCount K p : ℝ) ≤
      0.33 * (K : ℝ) := by
  intro X_small
  have hK1 := hK.hK1
  have hKpos := hK.Kpos
  have hlogK_pos := hK.logK_pos
  have hX1 : 1 ≤ X_small := by
    apply Nat.le_floor
    rw [Nat.cast_one]
    exact Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ K)) (by norm_num)
  have hX_le : (X_small : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 400) := Nat.floor_le (by positivity)
  set S_small := (3 * K).primesLE.filter (fun p => p ≤ X_small)
  have hsub : S_small ⊆ X_small.primesLE := by
    intro p hp
    simp only [S_small, mem_filter, Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.2, hp.1.2⟩
  have hterm : ∀ p ∈ S_small, Real.log (p : ℝ) * (NCount K p : ℝ) ≤
      33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesLE (mem_filter.mp hp).1
    have hpX : p ≤ X_small := (mem_filter.mp hp).2
    have hp_le_35 : ((p ^ 1 : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5) := by
      rw [pow_one]
      calc (p : ℝ) ≤ (X_small : ℝ) := by exact_mod_cast hpX
        _ ≤ (K : ℝ) ^ ((1 : ℝ) / 400) := hX_le
        _ ≤ (K : ℝ) ^ ((3 : ℝ) / 5) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ K)) (by norm_num)
    have hb := sec5_sieve_bound hK hp_prime le_rfl hp_le_35
    rw [pow_one] at hb
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
    calc Real.log (p : ℝ) * (NCount K p : ℝ)
        ≤ Real.log (p : ℝ) * (33 * (K : ℝ) / ((p : ℝ) * Real.log (K : ℝ))) :=
          mul_le_mul_of_nonneg_left hb hlogp_nn
      _ = 33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) := by ring
  calc ∑ p ∈ S_small, Real.log (p : ℝ) * (NCount K p : ℝ)
      ≤ ∑ p ∈ S_small, 33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ X_small.primesLE, 33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
          mul_nonneg (by positivity)
            (div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)) (by positivity))
    _ = 33 * (K : ℝ) / Real.log (K : ℝ) * ∑ p ∈ X_small.primesLE, Real.log (p : ℝ) / (p : ℝ) := by
        rw [← Finset.mul_sum]
    _ ≤ 33 * (K : ℝ) / Real.log (K : ℝ) * (4 * Real.log (X_small : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_primesLE_log_div_le X_small hX1) (by positivity)
    _ ≤ 33 * (K : ℝ) / Real.log (K : ℝ) * (4 * ((1 / 400 : ℝ) * Real.log (K : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h1 := Real.log_le_log (by exact_mod_cast (by omega : 0 < X_small)) hX_le
        rw [Real.log_rpow hKpos] at h1
        linarith
    _ = 0.33 * (K : ℝ) := by field_simp [hlogK_pos.ne']; ring

private lemma sec5_huge_zero {K : ℕ} (hK : LargeK K) (hno : ∀ k, K < k → ¬ HasCover k) :
    ∑ p ∈ (3 * K).primesLE.filter (fun p => 5 * K < p ^ 2), Real.log (p : ℝ) * (NCount K p : ℝ) = 0 := by
  have hK1 := hK.hK1
  refine Finset.sum_eq_zero fun Q hQ_mem => ?_
  have hQ := Nat.prime_of_mem_primesLE (mem_filter.mp hQ_mem).1
  have hQ2 : 5 * K < Q ^ 2 := (mem_filter.mp hQ_mem).2
  have hN0 : NCount K Q = 0 := by
    by_contra hne
    have hnon : ((PSet K).filter (fun q => Q ∣ q - 1)).Nonempty :=
      Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    obtain ⟨q, hq⟩ := hnon
    have hqP := (mem_filter.mp hq).1
    have hQdvd : Q ∣ q - 1 := (mem_filter.mp hq).2
    have hq_prime := (mem_filter.mp hqP).2
    have hq_Ioc := mem_Ioc.mp (mem_filter.mp hqP).1
    have hQ_gt2 : 2 < Q := by nlinarith
    have hq_gt2 : 2 < q := by omega
    have hq_odd : Odd q := hq_prime.odd_of_ne_two (by omega)
    have h2_dvd : 2 ∣ q - 1 := by
      obtain ⟨u, hu⟩ := hq_odd
      exact ⟨u, by omega⟩
    have h2Q_dvd : 2 * Q ∣ q - 1 :=
      ((Nat.coprime_primes Nat.prime_two hQ).mpr (by omega)).mul_dvd_of_dvd_of_dvd h2_dvd hQdvd
    have h2Q_le : 2 * Q ≤ q - 1 := Nat.le_of_dvd (by omega) h2Q_dvd
    have hcov := hasCover_of_prime_cluster (Q := Q) (r := 1) hQ le_rfl (fun _ => q)
      (fun x y _ => Subsingleton.elim x y)
      (fun _ => hq_prime)
      (fun _ => hQdvd)
      (fun _ => le_rfl)
      (fun _ => by rw [pow_one]; omega)
      (by rw [show 1 + 1 = 2 from rfl]; omega)
      (fun _ => by omega)
      (fun _ => by simp)
    exact hno (q + Q - 1) (by omega) hcov
  simp [hN0]

private lemma sec5_gap_bound {K : ℕ} (hK : LargeK K) :
    let X_small : ℕ := Nat.floor ((K : ℝ) ^ ((1 : ℝ) / 400))
    let S_med := (3 * K).primesLE.filter (fun p => X_small < p ∧ p ^ 2 ≤ 5 * K)
    ∑ p ∈ S_med.filter (IsGap K), Real.log (p : ℝ) * (NCount K p : ℝ) ≤ 0.05 * (K : ℝ) := by
  intro X_small S_med
  have hKpos := hK.Kpos
  have hlogK := hK.hlogK
  have hlogK_pos := hK.logK_pos
  set R : ℝ := (K : ℝ) ^ ((1 : ℝ) / 1000)
  have hR_big : (10000000 : ℝ) ≤ R := hK.hR_big
  have hR_pos : 0 < R := hK.R_pos
  have hR_pow : ∀ x : ℝ, (K : ℝ) ^ x = R ^ (1000 * x) := hK.R_pow
  set S_gap := S_med.filter (IsGap K)
  have hsqrt5_le_35 : Real.sqrt (5 * (K : ℝ)) ≤ (K : ℝ) ^ ((3 : ℝ) / 5) := by
    rw [Real.sqrt_eq_rpow, Real.mul_rpow (by norm_num) hKpos.le, hR_pow (1 / 2), hR_pow (3 / 5)]
    have h5 : (5 : ℝ) ^ ((1 : ℝ) / 2) ≤ 3 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]; norm_num
    have hR100 : 3 ≤ R ^ (100 : ℝ) := by
      calc (3 : ℝ) ≤ R := by linarith
        _ = R ^ (1 : ℝ) := (Real.rpow_one R).symm
        _ ≤ R ^ (100 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    calc (5 : ℝ) ^ ((1 : ℝ) / 2) * R ^ (1000 * ((1 : ℝ) / 2))
        ≤ R ^ (100 : ℝ) * R ^ (500 : ℝ) := by
          have : (1000 : ℝ) * (1 / 2) = 500 := by norm_num
          rw [this]; nlinarith [show (0 : ℝ) ≤ R ^ (500 : ℝ) by positivity]
      _ = R ^ (1000 * ((3 : ℝ) / 5)) := by rw [← Real.rpow_add hR_pos]; norm_num
  have hbiUnion_le : ∀ (M : Finset ℕ),
      ∑ Q ∈ S_med.filter (fun Q => ∃ m ∈ M, K < Q ^ m ∧ Q ^ m ≤ 5 * K),
        Real.log (Q : ℝ) * (NCount K Q : ℝ) ≤
      ∑ m ∈ M, ∑ Q ∈ S_med.filter (fun Q => K < Q ^ m ∧ Q ^ m ≤ 5 * K),
        Real.log (Q : ℝ) * (NCount K Q : ℝ) := by
    intro M
    let t : ℕ → Finset ℕ := fun m => S_med.filter (fun Q => K < Q ^ m ∧ Q ^ m ≤ 5 * K)
    let f : ℕ → ℝ := fun Q => Real.log (Q : ℝ) * (NCount K Q : ℝ)
    have hsub : S_med.filter (fun Q => ∃ m ∈ M, K < Q ^ m ∧ Q ^ m ≤ 5 * K) ⊆ M.biUnion t := by
      intro Q hQ
      simp only [t, mem_filter, mem_biUnion] at hQ ⊢
      obtain ⟨hQm, m, hm, h1, h2⟩ := hQ
      exact ⟨m, hm, hQm, h1, h2⟩
    have hnonneg : ∀ m ∈ M, ∀ Q ∈ t m, 0 ≤ f Q := by
      intro m _ Q hQ
      have hQp := Nat.prime_of_mem_primesLE (mem_filter.mp (mem_filter.mp hQ).1).1
      exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hQp.one_le)) (by positivity)
    have h1 : ∑ Q ∈ S_med.filter (fun Q => ∃ m ∈ M, K < Q ^ m ∧ Q ^ m ≤ 5 * K), f Q ≤
        ∑ Q ∈ M.biUnion t, f Q := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun Q hQ _ => ?_
      obtain ⟨m, hm, hQm⟩ := Finset.mem_biUnion.mp hQ
      exact hnonneg m hm Q hQm
    exact h1.trans (sum_biUnion_le_of_nonneg M t f hnonneg)
  have hsum_le : ∑ Q ∈ S_gap, Real.log (Q : ℝ) * (NCount K Q : ℝ) ≤
      ∑ m ∈ Icc 2 400, ∑ Q ∈ S_med.filter (fun Q => K < Q ^ m ∧ Q ^ m ≤ 5 * K),
        Real.log (Q : ℝ) * (NCount K Q : ℝ) := by
    have hEq : S_gap = S_med.filter (fun Q => ∃ m ∈ Icc 2 400, K < Q ^ m ∧ Q ^ m ≤ 5 * K) := by
      ext Q; simp only [S_gap, IsGap, mem_filter]
    rw [hEq]
    exact hbiUnion_le (Icc 2 400)
  have hm_bound : ∀ m ∈ Icc 2 400,
      ∑ Q ∈ S_med.filter (fun Q => K < Q ^ m ∧ Q ^ m ≤ 5 * K), Real.log (Q : ℝ) * (NCount K Q : ℝ) ≤
        33 * (K : ℝ) / Real.log (K : ℝ) * (5 * Real.log 4) := by
    intro m hm
    have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by have := (mem_Icc.mp hm).1; omega : 0 < m)
    have hm_ge2 : 2 ≤ m := (mem_Icc.mp hm).1
    set Sm := S_med.filter (fun Q => K < Q ^ m ∧ Q ^ m ≤ 5 * K)
    calc ∑ Q ∈ Sm, Real.log (Q : ℝ) * (NCount K Q : ℝ)
        ≤ ∑ Q ∈ Sm, 33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (Q : ℝ) / (Q : ℝ)) := by
          refine Finset.sum_le_sum fun Q hQ => ?_
          have hQmed := (mem_filter.mp hQ).1
          have hQp := Nat.prime_of_mem_primesLE (mem_filter.mp hQmed).1
          have hQ5K : Q ^ 2 ≤ 5 * K := (mem_filter.mp hQmed).2.2
          have hQ_le35 : ((Q ^ 1 : ℕ) : ℝ) ≤ (K : ℝ) ^ ((3 : ℝ) / 5) := by
            rw [pow_one]
            have h1 : (Q : ℝ) ≤ Real.sqrt (5 * (K : ℝ)) := by
              rw [Real.le_sqrt (by positivity) (by positivity)]
              exact_mod_cast hQ5K
            exact h1.trans hsqrt5_le_35
          have hb := sec5_sieve_bound hK hQp le_rfl hQ_le35
          rw [pow_one] at hb
          have hlogQ_nn : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast hQp.one_le)
          calc Real.log (Q : ℝ) * (NCount K Q : ℝ)
              ≤ Real.log (Q : ℝ) * (33 * (K : ℝ) / ((Q : ℝ) * Real.log (K : ℝ))) :=
                mul_le_mul_of_nonneg_left hb hlogQ_nn
            _ = 33 * (K : ℝ) / Real.log (K : ℝ) * (Real.log (Q : ℝ) / (Q : ℝ)) := by ring
      _ = 33 * (K : ℝ) / Real.log (K : ℝ) * ∑ Q ∈ Sm, Real.log (Q : ℝ) / (Q : ℝ) := by
          rw [← Finset.mul_sum]
      _ ≤ 33 * (K : ℝ) / Real.log (K : ℝ) * (5 * Real.log 4) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          set U : ℕ := Nat.floor ((5 * (K : ℝ)) ^ ((1 : ℝ) / (m : ℝ)))
          have hU_le : (U : ℝ) ≤ (5 * (K : ℝ)) ^ ((1 : ℝ) / (m : ℝ)) := Nat.floor_le (by positivity)
          calc ∑ Q ∈ Sm, Real.log (Q : ℝ) / (Q : ℝ)
              ≤ ∑ Q ∈ Sm, Real.log (Q : ℝ) / ((K : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by
                refine Finset.sum_le_sum fun Q hQ => ?_
                have hQp := Nat.prime_of_mem_primesLE (mem_filter.mp (mem_filter.mp hQ).1).1
                have hK_lt_Qm : K < Q ^ m := (mem_filter.mp hQ).2.1
                have hQ_ge : (K : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≤ (Q : ℝ) := by
                  have h1 : (K : ℝ) ≤ ((Q : ℝ) ^ m) := by exact_mod_cast hK_lt_Qm.le
                  have h2 := Real.rpow_le_rpow hKpos.le h1 (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ))
                  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
                    mul_one_div_cancel hm_pos.ne', Real.rpow_one] at h2
                  exact h2
                exact div_le_div_of_nonneg_left
                  (Real.log_nonneg (by exact_mod_cast hQp.one_le)) (by positivity) hQ_ge
            _ = (∑ Q ∈ Sm, Real.log (Q : ℝ)) / ((K : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by
                rw [← Finset.sum_div]
            _ ≤ (∑ Q ∈ U.primesLE, Real.log (Q : ℝ)) / ((K : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by
                apply div_le_div_of_nonneg_right _ (by positivity)
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro Q hQ
                  have hQp := Nat.prime_of_mem_primesLE (mem_filter.mp (mem_filter.mp hQ).1).1
                  have hQm_le : Q ^ m ≤ 5 * K := (mem_filter.mp hQ).2.2
                  rw [Nat.mem_primesLE]
                  refine ⟨Nat.le_floor ?_, hQp⟩
                  have h1 : ((Q : ℝ) ^ m) ≤ 5 * (K : ℝ) := by exact_mod_cast hQm_le
                  have h2 := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ))
                  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
                    mul_one_div_cancel hm_pos.ne', Real.rpow_one] at h2
                  exact h2
                · intro Q hQ _
                  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hQ).one_le)
            _ = Chebyshev.theta (U : ℝ) / ((K : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by
                rw [Chebyshev.theta_eq_sum_primesLE_log]
            _ ≤ (Real.log 4 * (U : ℝ)) / ((K : ℝ) ^ ((1 : ℝ) / (m : ℝ))) :=
                div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by positivity)) (by positivity)
            _ ≤ (Real.log 4 * (5 * (K : ℝ)) ^ ((1 : ℝ) / (m : ℝ))) / ((K : ℝ) ^ ((1 : ℝ) / (m : ℝ))) :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hU_le (by positivity)) (by positivity)
            _ = Real.log 4 * (5 : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
                rw [Real.mul_rpow (by norm_num) hKpos.le]
                field_simp [show (K : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≠ 0 by positivity]
            _ ≤ 5 * Real.log 4 := by
                have h5 : (5 : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≤ 5 := by
                  calc (5 : ℝ) ^ ((1 : ℝ) / (m : ℝ))
                      ≤ (5 : ℝ) ^ (1 : ℝ) :=
                        Real.rpow_le_rpow_of_exponent_le (by norm_num)
                          (by rw [div_le_one hm_pos]; exact_mod_cast (by omega : 1 ≤ m))
                    _ = 5 := Real.rpow_one 5
                nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  calc ∑ p ∈ S_gap, Real.log (p : ℝ) * (NCount K p : ℝ)
      ≤ ∑ _m ∈ Icc 2 400, (33 * (K : ℝ) / Real.log (K : ℝ) * (5 * Real.log 4)) :=
        hsum_le.trans (Finset.sum_le_sum hm_bound)
    _ = 399 * (33 * (K : ℝ) / Real.log (K : ℝ) * (5 * Real.log 4)) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; norm_num
    _ ≤ 0.05 * (K : ℝ) := by
        have hlog4_lt : Real.log (4 : ℝ) < 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow, Nat.cast_ofNat]
          linarith [Real.log_two_lt_d9]
        have h1 : 399 * (33 * (K : ℝ) / Real.log (K : ℝ) * (5 * Real.log 4)) =
            (399 * 33 * 5 * Real.log 4 * (K : ℝ)) / Real.log (K : ℝ) := by ring
        rw [h1, div_le_iff₀ hlogK_pos]
        nlinarith

private lemma sec5_good_single {K Q : ℕ} (hK : LargeK K) (hno : ∀ k, K < k → ¬ HasCover k)
    (hQp : Q.Prime) (hQX : Nat.floor ((K : ℝ) ^ ((1 : ℝ) / 400)) < Q)
    (hQ2_le : Q ^ 2 ≤ 5 * K) (hQ_notGap : ¬ IsGap K Q) :
    (NCount K Q : ℝ) ≤ 1600 * (K : ℝ) / ((Q : ℝ) ^ 2) + 4000 := by
  have hK1 := hK.hK1
  have hKpos := hK.Kpos
  set R : ℝ := (K : ℝ) ^ ((1 : ℝ) / 1000)
  have hR_big : (10000000 : ℝ) ≤ R := hK.hR_big
  have hR_pos : 0 < R := hK.R_pos
  have hR_pow : ∀ x : ℝ, (K : ℝ) ^ x = R ^ (1000 * x) := hK.R_pow
  have hK_eq_R : (K : ℝ) = R ^ (1000 : ℝ) := hK.K_eq_R
  set X_small : ℕ := Nat.floor ((K : ℝ) ^ ((1 : ℝ) / 400))
  have hX_ge2 : 2 ≤ X_small := by
    apply Nat.le_floor
    rw [hR_pow (1 / 400)]
    calc ((2 : ℕ) : ℝ) = 2 := by norm_num
      _ ≤ R := by linarith
      _ = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ R ^ (1000 * ((1 : ℝ) / 400)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hQ_ge3 : 3 ≤ Q := by omega
  set r := Nat.log Q (5 * K)
  have hr_ge2 : 2 ≤ r := Nat.le_log_of_pow_le hQp.one_lt hQ2_le
  have hr_le400 : r ≤ 400 := by
    by_contra! hgt
    have h1 : (K : ℝ) ^ ((1 : ℝ) / 400) < (Q : ℝ) := by
      have hfl : (K : ℝ) ^ ((1 : ℝ) / 400) < (X_small : ℝ) + 1 := Nat.lt_floor_add_one _
      have hX1 : (X_small : ℝ) + 1 ≤ (Q : ℝ) := by exact_mod_cast hQX
      linarith
    have h2 : (5 * (K : ℝ)) < ((Q : ℝ) ^ (401 : ℕ)) := by
      have hpow := Real.rpow_lt_rpow (by positivity) h1 (by norm_num : (0 : ℝ) < 401)
      rw [← Real.rpow_mul hKpos.le,
        show (401 : ℝ) = ((401 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hpow
      have h5K : 5 * (K : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 400 * ((401 : ℕ) : ℝ)) := by
        rw [hR_pow, hK_eq_R]
        have h5 : (5 : ℝ) ≤ R ^ ((5 : ℝ) / 2) := by
          calc (5 : ℝ) ≤ R := by linarith
            _ = R ^ (1 : ℝ) := (Real.rpow_one R).symm
            _ ≤ R ^ ((5 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        calc 5 * R ^ (1000 : ℝ) ≤ R ^ ((5 : ℝ) / 2) * R ^ (1000 : ℝ) :=
              mul_le_mul_of_nonneg_right h5 (by positivity)
          _ = R ^ (1000 * ((1 : ℝ) / 400 * ((401 : ℕ) : ℝ))) := by
              rw [← Real.rpow_add hR_pos]; norm_num
      linarith
    have h3 : 5 * K < Q ^ 401 := by exact_mod_cast h2
    have h4 : Q ^ 401 ≤ Q ^ r := Nat.pow_le_pow_right hQp.pos hgt
    have h5 : Q ^ r ≤ 5 * K := Nat.pow_log_le_self Q (by omega)
    omega
  have hQr_le_K : Q ^ r ≤ K := by
    have hQr_le5K : Q ^ r ≤ 5 * K := Nat.pow_log_le_self Q (by omega)
    by_contra! hgt
    exact hQ_notGap ⟨r, mem_Icc.mpr ⟨hr_ge2, hr_le400⟩, hgt, hQr_le5K⟩
  have h5K_lt_Qr1 : 5 * K < Q ^ (r + 1) := Nat.lt_pow_succ_log_self hQp.one_lt (5 * K)
  set Lb := min (Q ^ 2 - Q) (K / 4)
  have hLb_pos : 0 < Lb := by
    have h1 : 0 < Q ^ 2 - Q := Nat.sub_pos_of_lt (by nlinarith)
    have h2 : 0 < K / 4 := by omega
    exact lt_min h1 h2
  set PQ := (PSet K).filter (fun q => Q ∣ q - 1)
  have hmaps_b : ∀ q ∈ PQ, (q - K) / Lb ∈ range (2 * K / Lb + 1) := by
    intro q hq
    have hqIoc := mem_Ioc.mp (mem_filter.mp (mem_filter.mp hq).1).1
    rw [mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  have hbucket_lt : ∀ b ∈ range (2 * K / Lb + 1),
      (PQ.filter (fun q => (q - K) / Lb = b)).card < r := by
    intro b _
    by_contra! hge
    set B := PQ.filter (fun q => (q - K) / Lb = b)
    obtain ⟨B', hB'sub, hB'card⟩ := Finset.exists_subset_card_eq hge
    have hB'non : B'.Nonempty := Finset.card_pos.mp (by omega)
    let qmax := B'.max' hB'non
    have hqmax_mem : qmax ∈ B' := Finset.max'_mem B' hB'non
    have hB'rest_card : (B'.erase qmax).card = r - 1 := by
      rw [Finset.card_erase_of_mem hqmax_mem, hB'card]
    have hcard_coe : Fintype.card ↑(B'.erase qmax) = r - 1 := by
      rw [Fintype.card_coe]; exact hB'rest_card
    obtain ⟨e_rest⟩ := Fintype.truncEquivFinOfCardEq hcard_coe
    let f : Fin r → ℕ := fun t =>
      if h0 : t.val = 0 then qmax
      else (e_rest.symm ⟨t.val - 1, by omega⟩).val
    have hf_mem : ∀ t : Fin r, f t ∈ B' := by
      intro t
      dsimp only [f]
      split_ifs with h0
      · exact hqmax_mem
      · exact Finset.mem_of_mem_erase (e_rest.symm ⟨t.val - 1, by omega⟩).prop
    have hf_inj : Function.Injective f := by
      intro t1 t2 heq
      dsimp only [f] at heq
      split_ifs at heq with h1 h2 h2
      · exact Fin.ext (by omega)
      · exfalso
        have hne := (Finset.mem_erase.mp (e_rest.symm ⟨t2.val - 1, by omega⟩).prop).1
        exact hne heq.symm
      · exfalso
        have hne := (Finset.mem_erase.mp (e_rest.symm ⟨t1.val - 1, by omega⟩).prop).1
        exact hne heq
      · have hsub_eq : e_rest.symm ⟨t1.val - 1, by omega⟩ = e_rest.symm ⟨t2.val - 1, by omega⟩ :=
          Subtype.ext heq
        have hfin_eq := e_rest.symm.injective hsub_eq
        have hval := congrArg Fin.val hfin_eq
        dsimp only at hval
        exact Fin.ext (by omega)
    have hf0_eq : f ⟨0, by omega⟩ = qmax := by dsimp only [f]; rw [dif_pos rfl]
    have hf_in_B : ∀ t : Fin r, f t ∈ B := fun t => hB'sub (hf_mem t)
    have hf_prime : ∀ t, (f t).Prime := fun t =>
      (mem_filter.mp (mem_filter.mp (mem_filter.mp (hf_in_B t)).1).1).2
    have hf_dvd : ∀ t, Q ∣ f t - 1 := fun t =>
      (mem_filter.mp (mem_filter.mp (hf_in_B t)).1).2
    have hf_Ioc : ∀ t, K < f t ∧ f t ≤ 3 * K := fun t =>
      mem_Ioc.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp (hf_in_B t)).1).1).1
    have hf_le : ∀ t, f t ≤ f ⟨0, by omega⟩ := fun t => by
      rw [hf0_eq]; exact Finset.le_max' B' (f t) (hf_mem t)
    have hdiff_Lb : ∀ t, f ⟨0, by omega⟩ - f t < Lb := by
      intro t
      have hb0 : (f ⟨0, by omega⟩ - K) / Lb = b := (mem_filter.mp (hf_in_B ⟨0, by omega⟩)).2
      have hbt : (f t - K) / Lb = b := (mem_filter.mp (hf_in_B t)).2
      have h0_div := Nat.div_add_mod (f ⟨0, by omega⟩ - K) Lb
      have ht_div := Nat.div_add_mod (f t - K) Lb
      rw [hb0] at h0_div
      rw [hbt] at ht_div
      have h0_mod := Nat.mod_lt (f ⟨0, by omega⟩ - K) hLb_pos
      have hI0 := hf_Ioc ⟨0, by omega⟩
      have hIt := hf_Ioc t
      omega
    have hQ_lt_K2 : Q < K / 2 := by
      have : Q ^ 2 ≤ 5 * K := hQ2_le
      have hKdiv : K ≤ 2 * (K / 2) + 1 := by omega
      nlinarith
    have hk_lt_5K : f ⟨0, by omega⟩ + Q - 1 < 5 * K := by
      have := (hf_Ioc ⟨0, by omega⟩).2
      omega
    have hcov := hasCover_of_prime_cluster (Q := Q) (r := r) hQp (by omega) f hf_inj
      hf_prime hf_dvd hf_le
      (fun t => lt_of_le_of_lt hQr_le_K (hf_Ioc t).1)
      (hk_lt_5K.trans h5K_lt_Qr1)
      (fun t => by
        have hd := hdiff_Lb t
        have hLb_K4 : Lb ≤ K / 4 := min_le_right _ _
        have hI0 := (hf_Ioc ⟨0, by omega⟩).1
        have hle := hf_le t
        omega)
      (fun t => by
        have hd := hdiff_Lb t
        have hLb_Q2 : Lb ≤ Q ^ 2 - Q := min_le_left _ _
        omega)
    exact hno (f ⟨0, by omega⟩ + Q - 1) (by have := (hf_Ioc ⟨0, by omega⟩).1; omega) hcov
  have hcard_le : NCount K Q ≤ 400 * (2 * K / Lb + 1) := by
    have h1 : PQ.card = ∑ b ∈ range (2 * K / Lb + 1),
        (PQ.filter (fun q => (q - K) / Lb = b)).card := by
      rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise_of_maps_to hmaps_b]
      refine Finset.sum_congr rfl fun b _ => by simp
    calc NCount K Q = PQ.card := rfl
      _ = ∑ b ∈ range (2 * K / Lb + 1), (PQ.filter (fun q => (q - K) / Lb = b)).card := h1
      _ ≤ ∑ _b ∈ range (2 * K / Lb + 1), 400 := by
          refine Finset.sum_le_sum fun b hb => ?_
          have := hbucket_lt b hb
          omega
      _ = (2 * K / Lb + 1) * 400 := by simp
      _ = 400 * (2 * K / Lb + 1) := mul_comm _ _
  have h2K_Lb : ((2 * K / Lb : ℕ) : ℝ) ≤ 4 * (K : ℝ) / ((Q : ℝ) ^ 2) + 9 := by
    have hdiv_le : ((2 * K / Lb : ℕ) : ℝ) ≤ (2 * K : ℝ) / (Lb : ℝ) := by
      rw [le_div_iff₀ (by exact_mod_cast hLb_pos : (0 : ℝ) < Lb)]
      exact_mod_cast Nat.div_mul_le_self (2 * K) Lb
    rcases le_total (Q ^ 2 - Q) (K / 4) with hmin | hmin
    · have hLb_eq : Lb = Q ^ 2 - Q := min_eq_left hmin
      rw [hLb_eq] at hdiv_le ⊢
      have hQ2_half : ((Q : ℝ) ^ 2) / 2 ≤ ((Q ^ 2 - Q : ℕ) : ℝ) := by
        have hQle : Q ≤ Q ^ 2 := by nlinarith
        rw [Nat.cast_sub hQle]
        push_cast
        have : (3 : ℝ) ≤ Q := by exact_mod_cast hQ_ge3
        nlinarith
      have hstep : (2 * K : ℝ) / ((Q ^ 2 - Q : ℕ) : ℝ) ≤ (2 * K : ℝ) / (((Q : ℝ) ^ 2) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hQ2_half
      have heq : (2 * K : ℝ) / (((Q : ℝ) ^ 2) / 2) = 4 * (K : ℝ) / ((Q : ℝ) ^ 2) := by ring
      linarith
    · have hLb_eq : Lb = K / 4 := min_eq_right hmin
      rw [hLb_eq] at hdiv_le
      have hK4 : 2 * K / (K / 4) ≤ 9 := by
        rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < K / 4)]
        omega
      have h1 : ((2 * K / Lb : ℕ) : ℝ) ≤ 9 := by
        rw [hLb_eq]; exact_mod_cast hK4
      have hnn : (0 : ℝ) ≤ 4 * (K : ℝ) / ((Q : ℝ) ^ 2) := by positivity
      linarith
  have hcast : (NCount K Q : ℝ) ≤ 400 * (((2 * K / Lb : ℕ) : ℝ) + 1) := by
    exact_mod_cast hcard_le
  have hmul : 400 * (4 * (K : ℝ) / ((Q : ℝ) ^ 2)) = 1600 * (K : ℝ) / ((Q : ℝ) ^ 2) := by ring
  linarith

private lemma sec5_good_bound {K : ℕ} (hK : LargeK K) (hno : ∀ k, K < k → ¬ HasCover k) :
    let X_small : ℕ := Nat.floor ((K : ℝ) ^ ((1 : ℝ) / 400))
    let S_med := (3 * K).primesLE.filter (fun p => X_small < p ∧ p ^ 2 ≤ 5 * K)
    ∑ p ∈ S_med.filter (fun p => ¬ IsGap K p), Real.log (p : ℝ) * (NCount K p : ℝ) ≤ 0.05 * (K : ℝ) := by
  intro X_small S_med
  have hKpos := hK.Kpos
  set R : ℝ := (K : ℝ) ^ ((1 : ℝ) / 1000)
  have hR_big : (10000000 : ℝ) ≤ R := hK.hR_big
  have hR_pos : 0 < R := hK.R_pos
  have hlog3_le : Real.log (3 * (K : ℝ)) ≤ R := hK.log3_le
  have hR_pow : ∀ x : ℝ, (K : ℝ) ^ x = R ^ (1000 * x) := hK.R_pow
  have hK_eq_R : (K : ℝ) = R ^ (1000 : ℝ) := hK.K_eq_R
  set S_good := S_med.filter (fun p => ¬ IsGap K p)
  have hX_ge2 : 2 ≤ X_small := by
    apply Nat.le_floor
    rw [hR_pow (1 / 400)]
    calc ((2 : ℕ) : ℝ) = 2 := by norm_num
      _ ≤ R := by linarith
      _ = R ^ (1 : ℝ) := (Real.rpow_one R).symm
      _ ≤ R ^ (1000 * ((1 : ℝ) / 400)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hsub_Ioc : S_good ⊆ Ioc X_small (Nat.sqrt (5 * K)) := by
    intro Q hQ
    have hQmed := (mem_filter.mp hQ).1
    rw [mem_Ioc]
    exact ⟨(mem_filter.mp hQmed).2.1, Nat.le_sqrt.mpr (by simpa [sq] using (mem_filter.mp hQmed).2.2)⟩
  calc ∑ Q ∈ S_good, Real.log (Q : ℝ) * (NCount K Q : ℝ)
      ≤ ∑ Q ∈ S_good, R * (1600 * (K : ℝ) / ((Q : ℝ) ^ 2) + 4000) := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        have hQmed := (mem_filter.mp hQ).1
        have hQ_notGap : ¬ IsGap K Q := (mem_filter.mp hQ).2
        have hQp := Nat.prime_of_mem_primesLE (mem_filter.mp hQmed).1
        have hQle := Nat.le_of_mem_primesLE (mem_filter.mp hQmed).1
        have hQX : X_small < Q := (mem_filter.mp hQmed).2.1
        have hQ2_le : Q ^ 2 ≤ 5 * K := (mem_filter.mp hQmed).2.2
        have hlogQ : Real.log (Q : ℝ) ≤ R :=
          (Real.log_le_log (Nat.cast_pos.mpr hQp.pos) (by exact_mod_cast hQle)).trans hlog3_le
        exact mul_le_mul hlogQ (sec5_good_single hK hno hQp hQX hQ2_le hQ_notGap)
          (by positivity) hR_pos.le
    _ ≤ ∑ Q ∈ Ioc X_small (Nat.sqrt (5 * K)), R * (1600 * (K : ℝ) / ((Q : ℝ) ^ 2) + 4000) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_Ioc fun _ _ _ => by positivity
    _ = 1600 * (K : ℝ) * R * (∑ Q ∈ Ioc X_small (Nat.sqrt (5 * K)), ((Q : ℝ) ^ 2)⁻¹) +
          4000 * R * ((Ioc X_small (Nat.sqrt (5 * K))).card : ℝ) := by
        simp_rw [mul_add, Finset.sum_add_distrib, div_eq_mul_inv]
        congr 1
        · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
        · simp; ring
    _ ≤ 1600 * (K : ℝ) * R * (X_small : ℝ)⁻¹ + 4000 * R * (Nat.sqrt (5 * K) : ℝ) := by
        have h1 := sum_Ioc_inv_sq_le X_small (Nat.sqrt (5 * K)) (by omega)
        have h2 : ((Ioc X_small (Nat.sqrt (5 * K))).card : ℝ) ≤ (Nat.sqrt (5 * K) : ℝ) := by
          have : (Ioc X_small (Nat.sqrt (5 * K))).card ≤ Nat.sqrt (5 * K) := by simp
          exact_mod_cast this
        have hA := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1600 * (K : ℝ) * R)
        have hB := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4000 * R)
        linarith
    _ ≤ 0.05 * (K : ℝ) := by
        have hX_ge_R2 : R ^ 2 ≤ (X_small : ℝ) := by
          have h1 : (K : ℝ) ^ ((1 : ℝ) / 400) - 1 < (X_small : ℝ) := Nat.sub_one_lt_floor _
          have h2 : R ^ 2 + 1 ≤ (K : ℝ) ^ ((1 : ℝ) / 400) := by
            rw [hR_pow (1 / 400)]
            have h25 : (2 : ℝ) * R ^ 2 ≤ R ^ (1000 * ((1 : ℝ) / 400)) := by
              have hhalf : 2 ≤ R ^ ((1 : ℝ) / 2) := by
                have : (4 : ℝ) ≤ R := by linarith
                have := Real.rpow_le_rpow (by norm_num) this (by norm_num : (0 : ℝ) ≤ 1 / 2)
                rw [show (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 by
                  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
                    ← Real.rpow_mul (by norm_num)]; norm_num] at this
                exact this
              calc 2 * R ^ 2 ≤ R ^ ((1 : ℝ) / 2) * R ^ (2 : ℕ) :=
                    mul_le_mul_of_nonneg_right hhalf (by positivity)
                _ = R ^ (1000 * ((1 : ℝ) / 400)) := by
                    rw [← Real.rpow_natCast R 2, ← Real.rpow_add hR_pos]; norm_num
            nlinarith
          linarith
        have hterm1 : 1600 * (K : ℝ) * R * (X_small : ℝ)⁻¹ ≤ 0.02 * (K : ℝ) := by
          have hinv : (X_small : ℝ)⁻¹ ≤ (R ^ 2)⁻¹ := inv_anti₀ (by positivity) hX_ge_R2
          have hstep : 1600 * (K : ℝ) * R * (X_small : ℝ)⁻¹ ≤ 1600 * (K : ℝ) / R := by
            calc 1600 * (K : ℝ) * R * (X_small : ℝ)⁻¹
                ≤ 1600 * (K : ℝ) * R * (R ^ 2)⁻¹ :=
                  mul_le_mul_of_nonneg_left hinv (by positivity)
              _ = 1600 * (K : ℝ) / R := by field_simp [hR_pos.ne']
          have h2 : 1600 * (K : ℝ) / R ≤ 0.02 * (K : ℝ) := by
            rw [div_le_iff₀ hR_pos]; nlinarith
          linarith
        have hterm2 : 4000 * R * (Nat.sqrt (5 * K) : ℝ) ≤ 0.03 * (K : ℝ) := by
          have hsq : (Nat.sqrt (5 * K) : ℝ) ≤ 3 * (K : ℝ) ^ ((1 : ℝ) / 2) := by
            have h1 : ((Nat.sqrt (5 * K) : ℝ)) ^ 2 ≤ 5 * (K : ℝ) := by
              rw [sq]; exact_mod_cast Nat.sqrt_le (5 * K)
            have h2 : (Nat.sqrt (5 * K) : ℝ) ≤ Real.sqrt (5 * (K : ℝ)) := by
              rw [Real.le_sqrt (by positivity) (by positivity)]; exact h1
            have h3 : Real.sqrt (5 * (K : ℝ)) ≤ 3 * (K : ℝ) ^ ((1 : ℝ) / 2) := by
              rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (K : ℝ)]
              have : Real.sqrt 5 ≤ 3 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
              nlinarith [show (0 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 2) by positivity]
            linarith
          have hKR : R * (K : ℝ) ^ ((1 : ℝ) / 2) ≤ (K : ℝ) / R := by
            rw [le_div_iff₀ hR_pos, hR_pow (1 / 2), hK_eq_R]
            have h1 : R * R ^ (1000 * ((1 : ℝ) / 2)) * R = R ^ (502 : ℝ) := by
              calc R * R ^ (1000 * ((1 : ℝ) / 2)) * R
                  = R ^ (1 : ℝ) * R ^ (500 : ℝ) * R ^ (1 : ℝ) := by
                    rw [Real.rpow_one]; norm_num
                _ = R ^ (502 : ℝ) := by
                    rw [← Real.rpow_add hR_pos, ← Real.rpow_add hR_pos]; norm_num
            rw [h1]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          have h1 : 4000 * R * (Nat.sqrt (5 * K) : ℝ) ≤ 12000 * ((K : ℝ) / R) := by
            nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4000 * R)]
          have h2 : 12000 * ((K : ℝ) / R) ≤ 0.03 * (K : ℝ) := by
            rw [← mul_div_assoc, div_le_iff₀ hR_pos]; nlinarith
          linarith
        linarith

private lemma eventually_exists_hasCover_gt :
    ∀ᶠ K : ℕ in atTop, ∃ k, K < k ∧ HasCover k := by
  have h1 : ∀ᶠ K : ℕ in atTop, 100000 ≤ K := eventually_ge_atTop 100000
  have h2 : ∀ᶠ K : ℕ in atTop, Real.log (5 * (K : ℝ)) ≤ (K : ℝ) ^ ((1 : ℝ) / 1000) := by
    have ho := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 1000 by norm_num)).bound
      (show (0 : ℝ) < 1 / 2 by norm_num)
    have ht : Tendsto (fun K : ℕ => 5 * (K : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
    filter_upwards [ht.eventually ho, eventually_ge_atTop 10] with K hK hK10
    have hK10R : (10 : ℝ) ≤ K := by exact_mod_cast hK10
    have hKpos : (0 : ℝ) < K := by positivity
    rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)),
      Real.norm_of_nonneg (by positivity)] at hK
    have h5 : (5 : ℝ) ^ ((1 : ℝ) / 1000) ≤ 2 := by
      have : (5 : ℝ) ^ ((1 : ℝ) / 1000) ≤ (5 : ℝ) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have h5_lt : (5 : ℝ) ≤ (2 : ℝ) ^ (3 : ℕ) := by norm_num
      have h2 : (5 : ℝ) ^ (1 / 3 : ℝ) ≤ ((2 : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) h5_lt (by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h2
      norm_num at h2
      linarith
    rw [Real.mul_rpow (by norm_num) hKpos.le] at hK
    nlinarith [show (0 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 1000) by positivity]
  have h3 : ∀ᶠ K : ℕ in atTop, (10000000 : ℝ) ≤ Real.log (K : ℝ) := by
    have ht : Tendsto (fun K : ℕ => Real.log (K : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop 10000000)
  have h4 : ∀ᶠ K : ℕ in atTop, (10000000 : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 1000) := by
    have ht : Tendsto (fun K : ℕ => (K : ℝ) ^ ((1 : ℝ) / 1000)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_ge_atTop 10000000)
  filter_upwards [h1, h2, h3, h4] with K hK1 hlog5 hlogK hR_big
  by_contra hno
  push Not at hno
  have hK : LargeK K := ⟨hK1, hlog5, hlogK, hR_big⟩
  have hKpos := hK.Kpos
  set R : ℝ := (K : ℝ) ^ ((1 : ℝ) / 1000)
  have hR_pow : ∀ x : ℝ, (K : ℝ) ^ x = R ^ (1000 * x) := hK.R_pow
  have hK_eq_R : (K : ℝ) = R ^ (1000 : ℝ) := hK.K_eq_R
  set X_small : ℕ := Nat.floor ((K : ℝ) ^ ((1 : ℝ) / 400))
  set S_all := (3 * K).primesLE
  set S_small := S_all.filter (fun p => p ≤ X_small)
  set S_huge := S_all.filter (fun p => 5 * K < p ^ 2)
  set S_med := S_all.filter (fun p => X_small < p ∧ p ^ 2 ≤ 5 * K)
  set S_gap := S_med.filter (IsGap K)
  set S_good := S_med.filter (fun p => ¬ IsGap K p)
  have hpart : ∑ p ∈ S_all, Real.log (p : ℝ) * (NCount K p : ℝ) =
      (∑ p ∈ S_small, Real.log (p : ℝ) * (NCount K p : ℝ)) +
      (∑ p ∈ S_gap, Real.log (p : ℝ) * (NCount K p : ℝ)) +
      (∑ p ∈ S_good, Real.log (p : ℝ) * (NCount K p : ℝ)) +
      (∑ p ∈ S_huge, Real.log (p : ℝ) * (NCount K p : ℝ)) := by
    have h1 := (Finset.sum_filter_add_sum_filter_not S_all (fun p => p ≤ X_small)
      (fun p => Real.log (p : ℝ) * (NCount K p : ℝ))).symm
    have h2 : S_all.filter (fun p => ¬ p ≤ X_small) = S_med ∪ S_huge := by
      ext p; simp only [S_med, S_huge, mem_filter, mem_union]
      have : (X_small < p) ↔ ¬ p ≤ X_small := by omega
      constructor
      · intro ⟨hp, hgt⟩
        by_cases h5 : p ^ 2 ≤ 5 * K
        · exact Or.inl ⟨hp, this.mpr hgt, h5⟩
        · exact Or.inr ⟨hp, by omega⟩
      · rintro (⟨hp, hgt, _⟩ | ⟨hp, h5⟩)
        · exact ⟨hp, this.mp hgt⟩
        · refine ⟨hp, ?_⟩
          have hX_le : (X_small : ℝ) ≤ (K : ℝ) ^ ((1 : ℝ) / 400) := Nat.floor_le (by positivity)
          have hX2 : (X_small : ℝ) ^ 2 ≤ 5 * (K : ℝ) := by
            calc (X_small : ℝ) ^ 2 ≤ ((K : ℝ) ^ ((1 : ℝ) / 400)) ^ 2 := by nlinarith
              _ = R ^ (5 : ℝ) := by
                  rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le, hR_pow]; norm_num
              _ ≤ R ^ (1000 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
              _ ≤ 5 * (K : ℝ) := by rw [← hK_eq_R]; linarith
          have hX2N : X_small ^ 2 ≤ 5 * K := by exact_mod_cast hX2
          intro hle
          have : p ^ 2 ≤ X_small ^ 2 := Nat.pow_le_pow_left hle 2
          omega
    have hdisj : Disjoint S_med S_huge := by
      rw [Finset.disjoint_filter]
      intro p _ h1 h2; omega
    have h3 := (Finset.sum_filter_add_sum_filter_not S_med (IsGap K)
      (fun p => Real.log (p : ℝ) * (NCount K p : ℝ))).symm
    rw [h1, h2, Finset.sum_union hdisj, h3]
    ring
  have hlower := sec5_lower_bound hK
  have ha2_bound := sec5_ha2_bound hK
  have hsmall_bound := sec5_small_bound hK
  have hhuge_zero := sec5_huge_zero hK hno
  have hgap_bound := sec5_gap_bound hK
  have hgood_bound := sec5_good_bound hK hno
  have hdecomp := sum_log_sub_one_decomp K (by omega)
  dsimp only at hdecomp
  change ∑ q ∈ PSet K, Real.log ((q - 1 : ℕ) : ℝ) =
      (∑ p ∈ S_all, Real.log (p : ℝ) * (NCount K p : ℝ)) +
      (∑ p ∈ S_all, Real.log (p : ℝ) * ∑ a ∈ Icc 2 (Nat.log 2 (3 * K)), (NCount K (p ^ a) : ℝ)) at hdecomp
  linarith [hlower, hdecomp, hpart, hsmall_bound, hgap_bound, hgood_bound, hhuge_zero, ha2_bound]

end Erdos387H1B

theorem OMA.solution : OMA.R_Erdos387_erdos_387_variants_guy_R1.H1 := by
  apply Erdos387H1B.h1_of_frequently_hasCover
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨K, hKN, k, hKk, hcov⟩ :=
    (Filter.eventually_ge_atTop N |>.and Erdos387H1B.eventually_exists_hasCover_gt).exists
  exact ⟨k, le_of_lt (lt_of_le_of_lt hKN hKk), hcov⟩
