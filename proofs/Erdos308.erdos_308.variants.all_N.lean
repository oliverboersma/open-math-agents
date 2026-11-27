import FormalConjectures.ErdosProblems.«308»

/-! Arithmetic and combinatorial bounds for the all-height version of Erdős Problem 308. -/

open Finset

namespace Erdos308AllHeights

def mass (S : Finset ℕ) : ℚ := ∑ d ∈ S, (1 : ℚ) / d

def harmonicMass (n : ℕ) : ℚ := mass (Icc 1 n)

theorem mass_nonneg (S : Finset ℕ) : 0 ≤ mass S := by
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem mass_mono {S T : Finset ℕ} (h : S ⊆ T) : mass S ≤ mass T := by
  exact Finset.sum_le_sum_of_subset_of_nonneg h fun _ _ _ => by positivity

theorem mass_insert {S : Finset ℕ} {d : ℕ} (hd : d ∉ S) :
    mass (insert d S) = 1 / (d : ℚ) + mass S := by
  simp [mass, Finset.sum_insert hd]

theorem mass_sdiff {S T : Finset ℕ} (h : T ⊆ S) :
    mass (S \ T) = mass S - mass T := by
  unfold mass
  linarith [Finset.sum_sdiff (f := fun d : ℕ => (1 : ℚ) / d) h]

theorem mass_le_card (S : Finset ℕ) : mass S ≤ S.card := by
  calc
    mass S ≤ ∑ _ ∈ S, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro d _
      by_cases h : d = 0
      · simp [h]
      · have hp : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero h
        exact (div_le_iff₀ hp).2 (by simpa using (show (1 : ℚ) ≤ d by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h))
    _ = S.card := by simp

theorem power_dvd_lcmUpto {b p a : ℕ} (hb : 0 < b) (hp : p.Prime) :
    p ^ a ∣ Nat.lcmUpto b ↔ p ^ a ≤ b := by
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero b),
    Nat.factorization_lcmUpto b hp, Nat.le_log_iff_pow_le hp.one_lt hb.ne']

theorem dvd_lcmUpto_iff {b d : ℕ} (hb : 0 < b) (hd : 0 < d) :
    d ∣ Nat.lcmUpto b ↔ ∀ p a : ℕ, p.Prime → p ^ a ∣ d → p ^ a ≤ b := by
  constructor
  · intro h p a hp ha
    exact (power_dvd_lcmUpto hb hp).1 (ha.trans h)
  · intro h
    rw [← Nat.factorization_le_iff_dvd hd.ne' (Nat.lcmUpto_ne_zero b)]
    intro p
    by_cases hp : p.Prime
    · exact (hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero b)).1
        ((power_dvd_lcmUpto hb hp).2 (h p _ hp (Nat.ordProj_dvd d p)))
    · simp [Nat.factorization_eq_zero_of_not_prime d hp]

theorem lcmUpto_mono {a b : ℕ} (hab : a ≤ b) : Nat.lcmUpto a ∣ Nat.lcmUpto b := by
  unfold Nat.lcmUpto
  exact Finset.lcm_dvd fun d hd => Finset.dvd_lcm (Finset.Icc_subset_Icc_right hab hd)

theorem power_dvd_den_add {p a : ℕ} (hp : p.Prime) {x y : ℚ}
    (h : p ^ a ∣ (x + y).den) : p ^ a ∣ x.den ∨ p ^ a ∣ y.den := by
  have hh := h.trans (Rat.add_den_dvd_lcm x y)
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero x.den_pos.ne' y.den_pos.ne'),
    Nat.factorization_lcm x.den_pos.ne' y.den_pos.ne', Finsupp.sup_apply, le_sup_iff] at hh
  simpa only [hp.pow_dvd_iff_le_factorization x.den_pos.ne',
    hp.pow_dvd_iff_le_factorization y.den_pos.ne'] using hh

theorem power_dvd_den_sub {p a : ℕ} (hp : p.Prime) {x y : ℚ}
    (h : p ^ a ∣ (x - y).den) : p ^ a ∣ x.den ∨ p ^ a ∣ y.den := by
  rw [sub_eq_add_neg] at h
  simpa using power_dvd_den_add hp h

theorem power_dvd_den_mass {p a : ℕ} (hp : p.Prime) (ha : 0 < a) {S : Finset ℕ}
    (h : p ^ a ∣ (mass S).den) : ∃ d ∈ S, p ^ a ∣ d := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hp' : 1 < p ^ a := one_lt_pow₀ hp.one_lt ha.ne'
    have hd : p ^ a ∣ 1 := by simpa [mass] using h
    exact False.elim (hp'.not_ge (Nat.le_of_dvd (by decide) hd))
  | insert d S hd ih =>
    rw [mass_insert hd] at h
    rcases power_dvd_den_add hp h with h | h
    · refine ⟨d, mem_insert_self _ _, ?_⟩
      by_cases hzero : d = 0 <;> simp [one_div, hzero] at h ⊢
      exact h
    · obtain ⟨e, he, he'⟩ := ih h
      exact ⟨e, mem_insert_of_mem he, he'⟩

def admissible (n : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Icc 1 n ∧ (mass S).den ∣ Nat.lcmUpto n.sqrt

theorem exists_best (n : ℕ) : ∃ S, admissible n S ∧
    (∀ T, admissible n T → mass T ≤ mass S) ∧
    (∀ d ∈ Icc 1 n, d ∣ Nat.lcmUpto n.sqrt → d ∈ S) := by
  classical
  let family := (Icc 1 n).powerset.filter (fun S => (mass S).den ∣ Nat.lcmUpto n.sqrt)
  have hempty : ∅ ∈ family := by simp [family, mass]
  obtain ⟨S, hS, hbest⟩ := Finset.exists_max_image family mass ⟨∅, hempty⟩
  have hmem (T : Finset ℕ) : T ∈ family ↔ admissible n T := by
    simp [family, admissible]
  have hS' := (hmem S).1 hS
  refine ⟨S, hS', fun T hT => hbest T ((hmem T).2 hT), ?_⟩
  intro d hd hdvd
  by_contra hdS
  have hadd := mass_insert hdS
  have hden : ((1 : ℚ) / d).den ∣ Nat.lcmUpto n.sqrt := by
    have hd0 : 0 < d := by have := (Finset.mem_Icc.1 hd).1; omega
    simpa [one_div, Rat.inv_natCast_den, hd0.ne'] using hdvd
  have hnew : admissible n (insert d S) := by
    refine ⟨Finset.insert_subset hd hS'.1, ?_⟩
    rw [hadd]
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd hden hS'.2)
  have hpos : 0 < (1 : ℚ) / d := by
    have hd0 : 0 < d := by have := (Finset.mem_Icc.1 hd).1; omega
    positivity
  linarith [hbest _ ((hmem _).2 hnew)]

theorem harmonic_upper {q : ℕ} (hq : 2 ≤ q) : harmonicMass q ≤ (q : ℚ) / 3 + 5 / 6 := by
  have hsplit : Icc 1 q = insert 1 (insert 2 (Icc 3 q)) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hrest : mass (Icc 3 q) ≤ ((q : ℚ) - 2) / 3 := by
    calc
      mass (Icc 3 q) ≤ ∑ _ ∈ Icc 3 q, (1 : ℚ) / 3 := by
        apply Finset.sum_le_sum
        intro d hd
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast (Finset.mem_Icc.1 hd).1
      _ = ((q : ℚ) - 2) / 3 := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        have heq : q + 1 - 3 = q - 2 := by omega
        rw [heq, Nat.cast_sub hq]
        ring
  rw [harmonicMass, hsplit, mass_insert (by simp), mass_insert (by simp)]
  norm_num
  linarith

theorem mass_multiples {R : Finset ℕ} {q n : ℕ} (hq : 9 ≤ q) (hn : n ≤ q ^ 2)
    (hR : ∀ d ∈ R, d ∈ Icc 1 n ∧ q ∣ d) : mass R ≤ 23 / 54 := by
  let f : ℕ → ℕ := fun u => q * u
  have hq0 : (q : ℚ) ≠ 0 := by positivity
  have hsubset : R ⊆ (Icc 1 q).image f := by
    intro d hd
    obtain ⟨hdn, u, rfl⟩ := hR d hd
    have hd' := Finset.mem_Icc.1 hdn
    have hu : 1 ≤ u := by
      by_contra hh
      have : u = 0 := by omega
      simp [this] at hd'
    have hle : u ≤ q := by
      have : q * u ≤ q * q := hd'.2.trans (by simpa [pow_two] using hn)
      exact Nat.le_of_mul_le_mul_left this (by omega)
    exact Finset.mem_image.mpr ⟨u, Finset.mem_Icc.mpr ⟨hu, hle⟩, rfl⟩
  have hinj : Set.InjOn f (Icc 1 q : Finset ℕ) := by
    intro a _ b _ hab
    exact mul_left_cancel₀ (by omega : q ≠ 0) hab
  have hmass : mass ((Icc 1 q).image f) = harmonicMass q / q := by
    simp only [harmonicMass, mass]
    rw [Finset.sum_image (fun _ ha _ hb he => hinj ha hb he), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u hu
    simp [f, Nat.cast_mul, div_eq_mul_inv, mul_comm]
  calc
    mass R ≤ mass ((Icc 1 q).image f) := mass_mono hsubset
    _ = harmonicMass q / q := hmass
    _ ≤ 23 / 54 := by
      apply (div_le_iff₀ (by positivity : (0 : ℚ) < q)).2
      have h := harmonic_upper (by omega : 2 ≤ q)
      have hq' : (9 : ℚ) ≤ q := by exact_mod_cast hq
      linarith

theorem sq_bound_mul {q r n : ℕ} (hq : n ≤ q ^ 2) (hr : n ≤ r ^ 2)
    (hq0 : 0 < q) (hr0 : 0 < r) (hne : q ≠ r) : n < q * r := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact (by simpa [pow_two] using hq : n ≤ q * q).trans_lt
      (Nat.mul_lt_mul_of_pos_left h hq0)
  · exact (by simpa [pow_two] using hr : n ≤ r * r).trans_lt
      (Nat.mul_lt_mul_of_pos_right h hr0)

theorem change_height {N : ℕ} (hN : 64 ≤ N) {S : Finset ℕ}
    (hS : admissible (N + 1) S) :
    ∃ T, admissible N T ∧ mass S ≤ mass T + 23 / 54 := by
  classical
  let Bad := fun q : ℕ => IsPrimePow q ∧ q ∣ N + 1 ∧ N < q ^ 2
  have hsqrt : 0 < N.sqrt := Nat.sqrt_pos.2 (by omega)
  have hsqrt' : 0 < (N + 1).sqrt := Nat.sqrt_pos.2 (by omega)
  by_cases hex : ∃ q, Bad q
  · let q := Nat.find hex
    have spec : Bad q := Nat.find_spec hex
    obtain ⟨hqpow, hqd, hhigh⟩ := spec
    obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff _).1 hqpow
    have hqpos : 0 < q := by rw [← hpa]; exact pow_pos hp.pos _
    have hqN : N + 1 ≤ q ^ 2 := by omega
    have hq9 : 9 ≤ q := by
      by_contra! h
      have : q ^ 2 ≤ 8 ^ 2 := Nat.pow_le_pow_left (by omega) 2
      norm_num at this
      omega
    let R := S.filter (fun d => q ∣ d)
    let T := S \ R
    have hRS : R ⊆ S := Finset.filter_subset _ _
    refine ⟨T, ⟨?_, ?_⟩, ?_⟩
    · intro d hd
      have hd' := Finset.mem_sdiff.1 hd
      have hnmem := Finset.mem_Icc.1 (hS.1 hd'.1)
      have hne : d ≠ N + 1 := by
        intro he
        exact hd'.2 (Finset.mem_filter.mpr ⟨hd'.1, he ▸ hqd⟩)
      exact Finset.mem_Icc.mpr ⟨hnmem.1, by omega⟩
    · apply (dvd_lcmUpto_iff hsqrt (mass T).den_pos).2
      intro r b hr hrd
      by_contra! hlarge
      have hb : 0 < b := by
        by_contra! h
        have : b = 0 := by omega
        simp [this] at hlarge
        omega
      have hrN : N + 1 ≤ (r ^ b) ^ 2 := by
        have := Nat.sqrt_lt'.1 hlarge
        omega
      by_cases hrp : r = p
      · subst r
        have hqle : q ≤ p ^ b := by
          by_contra! h
          have hab : b ≤ a := by
            rw [← hpa] at h
            exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 h |>.le
          have hd : p ^ b ∣ N + 1 := (pow_dvd_pow p hab).trans (hpa ▸ hqd)
          exact (Nat.find_min hex h) ⟨(isPrimePow_nat_iff _).2 ⟨p, b, hp, hb, rfl⟩, hd, Nat.sqrt_lt'.1 hlarge⟩
        have hab : a ≤ b := by
          rw [← hpa] at hqle
          exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hqle
        obtain ⟨d, hd, hdd⟩ := power_dvd_den_mass hp hb hrd
        have hd' := Finset.mem_sdiff.1 hd
        exact hd'.2 (Finset.mem_filter.mpr ⟨hd'.1, hpa ▸ (pow_dvd_pow p hab).trans hdd⟩)
      · have hcop : q.Coprime (r ^ b) := by
          rw [← hpa]
          exact Nat.coprime_pow_primes _ _ hp hr (Ne.symm hrp)
        have hne : q ≠ r ^ b := by
          intro he
          rw [← he, Nat.coprime_self] at hcop
          omega
        have hprod := sq_bound_mul hqN hrN hqpos (pow_pos hr.pos _) hne
        have hstrict : N + 1 < (r ^ b) ^ 2 := by
          by_contra! h
          have he : (r ^ b) ^ 2 = N + 1 := le_antisymm h hrN
          have hdiv : r ^ b ∣ N + 1 := he ▸ (by rw [pow_two]; exact dvd_mul_right _ _)
          exact (not_le_of_gt hprod) (Nat.le_of_dvd (by omega)
            (hcop.mul_dvd_of_dvd_of_dvd hqd hdiv))
        have hms : mass T = mass S - mass R := mass_sdiff hRS
        rw [hms] at hrd
        rcases power_dvd_den_sub hr hrd with h | h
        · have hle := (power_dvd_lcmUpto hsqrt' hr).1 (h.trans hS.2)
          exact (Nat.sqrt_lt'.2 hstrict).not_ge hle
        · obtain ⟨d, hd, hdiv⟩ := power_dvd_den_mass hr hb h
          obtain ⟨hds, hqdiv⟩ := Finset.mem_filter.1 hd
          have hmult := hcop.mul_dvd_of_dvd_of_dvd hqdiv hdiv
          have hbnd := Finset.mem_Icc.1 (hS.1 hds)
          exact (not_le_of_gt hprod) ((Nat.le_of_dvd (by omega) hmult).trans hbnd.2)
    · have hbd : mass R ≤ 23 / 54 := mass_multiples hq9 hqN fun d hd =>
        ⟨hS.1 (Finset.mem_filter.1 hd).1, (Finset.mem_filter.1 hd).2⟩
      have hms : mass T = mass S - mass R := mass_sdiff hRS
      linarith
  · let R := S.filter (fun d => d = N + 1)
    let T := S \ R
    have hRS : R ⊆ S := Finset.filter_subset _ _
    refine ⟨T, ⟨?_, ?_⟩, ?_⟩
    · intro d hd
      have hd' := Finset.mem_sdiff.1 hd
      have hdi := Finset.mem_Icc.1 (hS.1 hd'.1)
      have hne : d ≠ N + 1 := fun he => hd'.2 (Finset.mem_filter.2 ⟨hd'.1, he⟩)
      exact Finset.mem_Icc.mpr ⟨hdi.1, by omega⟩
    · apply (dvd_lcmUpto_iff hsqrt (mass T).den_pos).2
      intro p a hp hd
      by_contra! hlarge
      have ha : 0 < a := by
        by_contra! h
        have : a = 0 := by omega
        simp [this] at hlarge
        omega
      have hpow := (isPrimePow_nat_iff (p ^ a)).2 ⟨p, a, hp, ha, rfl⟩
      have hgt := Nat.sqrt_lt'.1 hlarge
      have hstrict : N + 1 < (p ^ a) ^ 2 := by
        by_contra! h
        have he : (p ^ a) ^ 2 = N + 1 := le_antisymm h (by omega)
        have hpN : p ^ a ∣ N + 1 := he ▸ (by rw [pow_two]; exact dvd_mul_right _ _)
        exact hex ⟨_, hpow, hpN, hgt⟩
      have hms : mass T = mass S - mass R := mass_sdiff hRS
      rw [hms] at hd
      rcases power_dvd_den_sub hp hd with h | h
      · exact (Nat.sqrt_lt'.2 hstrict).not_ge ((power_dvd_lcmUpto hsqrt' hp).1 (h.trans hS.2))
      · obtain ⟨d, hdm, hd⟩ := power_dvd_den_mass hp ha h
        have he := (Finset.mem_filter.1 hdm).2
        exact hex ⟨_, hpow, he ▸ hd, hgt⟩
    · have hsingle : R ⊆ {N + 1} := by
        intro d hd
        simpa only [Finset.mem_singleton] using (Finset.mem_filter.1 hd).2
      have hbound := mass_mono hsingle
      change mass R ≤ mass {N + 1} at hbound
      have hsinglemass : mass {N + 1} = (1 : ℚ) / (↑(N + 1 : ℕ) : ℚ) := by simp [mass]
      rw [hsinglemass] at hbound
      have hmass : mass T = mass S - mass R := mass_sdiff hRS
      have hnq : (65 : ℚ) ≤ ((N + 1 : ℕ) : ℚ) := by exact_mod_cast (show 65 ≤ N + 1 by omega)
      have hfrac := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 65) hnq
      linarith

open Erdos308 (IsRepresentable)

def ClosedBelow (N : ℕ) : Prop :=
  ∀ j k : ℕ, 0 < j → j < k → IsRepresentable N k → IsRepresentable N j

theorem rep_mono {n N k : ℕ} (h : n ≤ N) (hrep : IsRepresentable n k) :
    IsRepresentable N k := by
  obtain ⟨S, hS, hm⟩ := hrep
  exact ⟨S, hS.trans (Finset.Icc_subset_Icc_right h), hm⟩

theorem rep_upper {n k : ℕ} (h : IsRepresentable n k) : (k : ℚ) ≤ harmonicMass n := by
  obtain ⟨S, hS, hm⟩ := h
  exact hm ▸ mass_mono hS

theorem rep_one {n : ℕ} (hn : 1 ≤ n) : IsRepresentable n 1 := by
  refine ⟨{1}, ?_, by simp⟩
  simpa [Finset.singleton_subset_iff, Finset.mem_Icc] using hn

theorem rep_two {n : ℕ} (hn : 6 ≤ n) : IsRepresentable n 2 := by
  apply rep_mono hn
  refine ⟨{1, 2, 3, 6}, by decide, ?_⟩
  norm_num [Finset.sum_insert, Finset.sum_singleton]

theorem erase_one {n k : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 n)
    (hm : mass S = k) (hk : 0 < k) (h : 1 ∈ S) : IsRepresentable n (k - 1) := by
  have hsub : ({1} : Finset ℕ) ⊆ S := Finset.singleton_subset_iff.mpr h
  refine ⟨S \ {1}, Finset.sdiff_subset.trans hS, ?_⟩
  change mass (S \ {1}) = _
  rw [mass_sdiff hsub, hm, Nat.cast_sub hk, show mass {1} = 1 by norm_num [mass]]
  simp

theorem insert_one_rep {n k : ℕ} {S : Finset ℕ} (hn : 1 ≤ n) (hS : S ⊆ Icc 1 n)
    (hm : mass S = k) (h : 1 ∉ S) : IsRepresentable n (k + 1) := by
  refine ⟨insert 1 S, Finset.insert_subset (Finset.mem_Icc.2 ⟨by rfl, hn⟩) hS, ?_⟩
  change mass (insert 1 S) = _
  simp [mass_insert h, hm, add_comm]

set_option maxRecDepth 30000 in
set_option maxHeartbeats 3000000 in
theorem harmonic64 : harmonicMass 64 < 5 := by
  decide +kernel

theorem closed_below_small {n : ℕ} (hn : 1 ≤ n) (hn64 : n ≤ 64) : ClosedBelow n := by
  intro j k hj hjk hrep
  by_cases h6 : n < 6
  · have h5 : harmonicMass n ≤ harmonicMass 5 :=
      mass_mono (Finset.Icc_subset_Icc_right (by omega))
    have hh : harmonicMass 5 < 3 := by decide +kernel
    have hk' : (k : ℚ) < 3 := (rep_upper hrep).trans_lt (h5.trans_lt hh)
    have hk : k < 3 := by exact_mod_cast hk'
    have hj' : j = 1 := by omega
    simpa [hj'] using rep_one hn
  · have h64 : harmonicMass n ≤ harmonicMass 64 := mass_mono (Finset.Icc_subset_Icc_right hn64)
    have hk' : (k : ℚ) < 5 := (rep_upper hrep).trans_lt (h64.trans_lt harmonic64)
    have hk : k < 5 := by exact_mod_cast hk'
    have hj3 : j ≤ 3 := by omega
    interval_cases j
    · exact rep_one hn
    · exact rep_two (by omega)
    · have h4 : k = 4 := by omega
      subst k
      obtain ⟨S, hS, hm⟩ := hrep
      have h1 : 1 ∈ S := by
        by_contra hh
        have h5 := rep_upper (insert_one_rep hn hS hm hh)
        norm_num at h5
        linarith [harmonic64]
      exact erase_one hS hm (by decide : 0 < (4 : ℕ)) h1

theorem step_closed {N z : ℕ} (hn : 1 ≤ N) (hclosed : ClosedBelow N)
    (hz : IsRepresentable N z) (hbound : ∀ k, IsRepresentable (N + 1) k → k ≤ z + 2) :
    ClosedBelow (N + 1) := by
  intro j k hj hjk hk
  by_cases hjz : j ≤ z
  · by_cases he : j = z
    · exact rep_mono (by omega) (he ▸ hz)
    · exact rep_mono (by omega) (hclosed j z hj (by omega) hz)
  · have hkj : k - 1 = j := by have := hbound k hk; omega
    obtain ⟨S, hS, hm⟩ := hk
    have h1 : 1 ∈ S := by
      by_contra hh
      have := hbound (k + 1) (insert_one_rep (by omega) hS hm hh)
      omega
    exact hkj ▸ erase_one hS hm (by omega) h1

theorem interval_of_closed {N : ℕ} (hclosed : ClosedBelow N) :
    ∃ m, Erdos308.representable N = Set.Icc 1 m := by
  classical
  let family := (Finset.range (N + 1)).filter (IsRepresentable N)
  have hzero : 0 ∈ family := by
    apply Finset.mem_filter.2
    exact ⟨Finset.mem_range.2 (by omega), ⟨∅, Finset.empty_subset _, by simp⟩⟩
  have hmem (k : ℕ) : IsRepresentable N k ↔ k ∈ family := by
    constructor
    · intro hr
      obtain ⟨S, hS, hm⟩ := hr
      have hcard := mass_le_card S
      rw [show mass S = (k : ℚ) from hm] at hcard
      have hk : k ≤ S.card := by exact_mod_cast hcard
      have hc := Finset.card_le_card hS
      rw [Nat.card_Icc] at hc
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ⟨S, hS, hm⟩⟩
    · exact fun hk => (Finset.mem_filter.1 hk).2
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image family id ⟨0, hzero⟩
  refine ⟨m, ?_⟩
  ext k
  change (0 < k ∧ IsRepresentable N k) ↔ 1 ≤ k ∧ k ≤ m
  constructor
  · exact fun ⟨h, hr⟩ => ⟨by omega, hmax _ ((hmem _).1 hr)⟩
  · intro ⟨hk, hkm⟩
    refine ⟨by omega, ?_⟩
    rcases hkm.lt_or_eq with hl | rfl
    · exact hclosed _ _ (by omega) hl ((hmem _).2 hm)
    · exact (hmem _).2 hm

theorem sum_cost_le (q : ℕ) :
    (∑ j ∈ Finset.Icc 2 q, if j ≤ 10 then (1 : ℚ) / j else 6 / (j : ℚ)^2)
      ≤ (4861/2520 + 3/5 : ℚ) := by
  let cost (j : ℕ) : ℚ := if j ≤ 10 then 1 / j else 6 / (j : ℚ)^2
  change (∑ j ∈ Icc 2 q, cost j) ≤ _
  have hten : (∑ j ∈ Icc 2 10, cost j) = 4861/2520 := by
    unfold cost
    decide +kernel
  by_cases hq : q ≤ 10
  · have h := Finset.sum_le_sum_of_subset_of_nonneg (f := cost)
        (Icc_subset_Icc_right hq : Icc 2 q ⊆ Icc 2 10)
        (fun i _ _ => by unfold cost; split <;> positivity)
    linarith
  · have H (n : ℕ) (hn : 10 ≤ n) :
        (∑ j ∈ Icc 2 n, cost j) + 6 / (n : ℚ) ≤ 4861/2520 + 3/5 := by
      induction n, hn using Nat.le_induction with
      | base => rw [hten]; norm_num
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n + 1)]
        have he : cost (n+1) = 6 / ((n : ℚ)+1)^2 := by simp [cost, show ¬n+1≤10 by omega]
        rw [he, Nat.cast_succ]
        have hpos : (0 : ℚ) < n := by exact_mod_cast (show 0 < n by omega)
        have hdiff : 6 / ((n : ℚ)+1)^2 + 6 / ((n : ℚ)+1) ≤ 6 / (n : ℚ) := by
          field_simp
          nlinarith
        linarith
    have := H q (by omega)
    have hz : (0 : ℚ) ≤ 6 / (q : ℚ) := by positivity
    linarith

theorem lcm_no_power {q : ℕ} (hq : 2 ≤ q) (hn : ¬ IsPrimePow q) :
    Nat.lcmUpto q = Nat.lcmUpto (q - 1) := by
  apply Nat.eq_of_factorization_eq (Nat.lcmUpto_ne_zero _) (Nat.lcmUpto_ne_zero _)
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_lcmUpto _ hp, Nat.factorization_lcmUpto _ hp]
    have hqeq : q - 1 + 1 = q := by omega
    have hh : p.log (q - 1) = p.log (q - 1 + 1) := by
      apply (Nat.log_eq_log_succ_iff hp.one_lt (by omega : q - 1 ≠ 0)).2
      rw [hqeq]
      intro he
      have hl : 0 < p.log q := by
        by_contra! h
        have h0 : p.log q = 0 := by omega
        rw [h0, pow_zero] at he
        omega
      exact hn ((isPrimePow_nat_iff _).2 ⟨p, _, hp, hl, he⟩)
    simpa only [hqeq] using hh.symm
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem lcm_power {p a : ℕ} (hp : p.Prime) (ha : 0 < a) :
    Nat.lcmUpto (p ^ a) = p * Nat.lcmUpto (p ^ a - 1) := by
  have hq : 1 < p ^ a := one_lt_pow₀ hp.one_lt ha.ne'
  apply Nat.eq_of_factorization_eq (Nat.lcmUpto_ne_zero _)
    (mul_ne_zero hp.ne_zero (Nat.lcmUpto_ne_zero _))
  intro r
  rw [Nat.factorization_mul hp.ne_zero (Nat.lcmUpto_ne_zero _), Finsupp.add_apply]
  by_cases hr : r.Prime
  · rw [Nat.factorization_lcmUpto _ hr, Nat.factorization_lcmUpto _ hr]
    by_cases he : r = p
    · subst r
      rw [hp.factorization_self, Nat.log_pow hp.one_lt]
      have hlo : a - 1 ≤ p.log (p ^ a - 1) := by
        apply (Nat.le_log_iff_pow_le hp.one_lt (by omega)).2
        have hlt : p ^ (a - 1) < p ^ a :=
          (Nat.pow_lt_pow_iff_right hp.one_lt).2 (by omega)
        omega
      have hhi : p.log (p ^ a - 1) < a := by
        apply Nat.log_lt_of_lt_pow (by omega)
        omega
      omega
    · have hp0 : p.factorization r = 0 := by simp [hp.factorization, he]
      rw [hp0, zero_add]
      have hs : p ^ a - 1 + 1 = p ^ a := by omega
      have hh : r.log (p ^ a - 1) = r.log (p ^ a - 1 + 1) := by
        apply (Nat.log_eq_log_succ_iff hr.one_lt (by omega : p ^ a - 1 ≠ 0)).2
        rw [hs]
        intro h
        have hb : 0 < r.log (p ^ a) := by
          by_contra! hh
          have h0 : r.log (p ^ a) = 0 := by omega
          rw [h0, pow_zero] at h
          omega
        have hrd : r ∣ p := hr.dvd_of_dvd_pow
          (h ▸ (dvd_pow_self r hb.ne' : r ∣ r ^ r.log (p ^ a)))
        exact he ((Nat.prime_dvd_prime_iff_eq hr hp).1 hrd)
      simpa only [hs] using hh.symm
  · simp [Nat.factorization_eq_zero_of_not_prime _ hr]

theorem lcm_member {b d : ℕ} (hd : 0 < d) (hdb : d ≤ b) : d ∣ Nat.lcmUpto b := by
  unfold Nat.lcmUpto
  exact Finset.dvd_lcm (Finset.mem_Icc.2 ⟨hd, hdb⟩)

theorem den_as_integer_fraction {x : ℚ} {L : ℕ} (h : x.den ∣ L) (hL : L ≠ 0) :
    ∃ m : ℤ, x = (m : ℚ) / (L : ℚ) := by
  obtain ⟨k, hk⟩ := h
  have hk0 : k ≠ 0 := by intro h0; apply hL; simp [hk, h0]
  refine ⟨x.num * (k : ℤ), ?_⟩
  calc
    x = (x.num : ℚ) / x.den := (Rat.num_div_den x).symm
    _ = ((x.num * (k : ℤ) : ℤ) : ℚ) / (L : ℚ) := by
      rw [hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
      exact (mul_div_mul_right _ _ (by exact_mod_cast hk0 : (k : ℚ) ≠ 0)).symm

theorem den_from_fraction {x : ℚ} {m : ℤ} {L : ℕ} (h : x = (m : ℚ) / (L : ℚ)) :
    x.den ∣ L := by
  apply Int.natCast_dvd_natCast.1
  have hh := Rat.den_dvd m (L : ℤ)
  simpa only [← Rat.intCast_div_eq_divInt, Int.cast_natCast, ← h] using hh

theorem scaled_mass {S : Finset ℕ} {L : ℕ} (h : ∀ d ∈ S, 0 < d ∧ d ∣ L) :
    (L : ℚ) * mass S = (↑(∑ d ∈ S, L / d) : ℚ) := by
  rw [mass, Finset.mul_sum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Rat.natCast_div _ _ (h _ hd).2]
  ring

theorem weight_mod {p a c : ℕ} [Fact p.Prime] (hp : p.Prime) (hc : 0 < c)
    (hcq : c < p ^ a) (hcp : ¬ p ∣ c) :
    p ^ a * c ∣ Nat.lcmUpto (p ^ a) ∧
    ((Nat.lcmUpto (p ^ a) / (p ^ a * c) : ℕ) : ZMod p) =
      ((Nat.lcmUpto (p ^ a) / p ^ a : ℕ) : ZMod p) * (c : ZMod p)⁻¹ := by
  let q := p ^ a
  let L := Nat.lcmUpto q
  have hq : 0 < q := pow_pos hp.pos _
  have hqL : q ∣ L := lcm_member hq le_rfl
  have hcL : c ∣ L := lcm_member hc hcq.le
  have hcop : q.Coprime c := (hp.coprime_iff_not_dvd.2 hcp).pow_left _
  have hd : q * c ∣ L := hcop.mul_dvd_of_dvd_of_dvd hqL hcL
  refine ⟨hd, ?_⟩
  change ((L / (q * c) : ℕ) : ZMod p) = ((L / q : ℕ) : ZMod p) * (c : ZMod p)⁻¹
  have hc0 : (c : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.natCast_eq_zero_iff]
  apply (eq_mul_inv_iff_mul_eq₀ hc0).2
  have hnat : L / (q * c) * c = L / q := by
    apply mul_right_cancel₀ hq.ne'
    rw [mul_assoc, mul_comm c q, Nat.div_mul_cancel hd, Nat.div_mul_cancel hqL]
  rw [← Nat.cast_mul, hnat]

def stepCost (q : ℕ) : ℚ := if q ≤ 10 then 1 / (q : ℚ) else 6 / (q : ℚ)^2

def CofactorSelection : Prop :=
  ∀ (p a : ℕ) [Fact p.Prime], p.Prime → 0 < a → ∀ r : ZMod p,
    ∃ C : Finset ℕ, (∀ c ∈ C, 0 < c ∧ c < p ^ a ∧ ¬ p ∣ c) ∧
      (∑ c ∈ C, (c : ZMod p)⁻¹) = r ∧
      (∑ c ∈ C, (1 : ℚ) / ((p ^ a * c : ℕ) : ℚ)) ≤ stepCost (p ^ a)

theorem cost_nonneg (q : ℕ) : 0 ≤ stepCost q := by
  unfold stepCost
  split <;> positivity

theorem cancellation_step (select : CofactorSelection) {N p a : ℕ} (hp : p.Prime)
    (ha : 0 < a) (hN : (p ^ a) ^ 2 ≤ N) {S : Finset ℕ}
    (hden : (mass S).den ∣ Nat.lcmUpto (p ^ a))
    (hres : ∀ d ∈ Icc 1 N, d ∣ Nat.lcmUpto (p ^ a) → d ∈ S) :
    ∃ T ⊆ S, (mass T).den ∣ Nat.lcmUpto (p ^ a - 1) ∧
      (∀ d ∈ Icc 1 N, d ∣ Nat.lcmUpto (p ^ a - 1) → d ∈ T) ∧
      mass S - mass T ≤ stepCost (p ^ a) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let q := p ^ a
  let L := Nat.lcmUpto q
  let B := Nat.lcmUpto (q - 1)
  have hq : 1 < q := one_lt_pow₀ hp.one_lt ha.ne'
  have hL : L ≠ 0 := Nat.lcmUpto_ne_zero _
  have hLB : L = p * B := lcm_power hp ha
  have hqL : q ∣ L := lcm_member (by omega) le_rfl
  have hv : ((L / q : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_div_iff_mul_dvd hqL]
    intro h
    have hd : p ^ (a + 1) ∣ Nat.lcmUpto q := by
      simpa [q, L, pow_succ, mul_comm] using h
    have hh := (power_dvd_lcmUpto (by omega : 0 < q) hp).1 hd
    exact (Nat.pow_lt_pow_iff_right hp.one_lt).2 (show a < a + 1 by omega) |>.not_ge hh
  obtain ⟨m, hm⟩ := den_as_integer_fraction hden hL
  change mass S = (m : ℚ) / (L : ℚ) at hm
  let v : ZMod p := (L / q : ℕ)
  obtain ⟨C, hC, hsumC, hcost⟩ := select p a hp ha ((m : ZMod p) / v)
  let f := fun c : ℕ => q * c
  let D := C.image f
  have hinj : Function.Injective f := fun _ _ he => mul_left_cancel₀ (by omega : q ≠ 0) he
  have hdata (d : ℕ) (hd : d ∈ D) : d ∈ Icc 1 N ∧ d ∣ L ∧ q ∣ d := by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨hc0, hcq, hcp⟩ := hC c hc
    have hdL := (weight_mod hp hc0 hcq hcp).1
    have hdN : q * c ≤ N := (Nat.mul_le_mul_left q hcq.le).trans (by simpa [q, pow_two] using hN)
    exact ⟨Finset.mem_Icc.2 ⟨Nat.mul_pos (by omega : 0 < q) hc0, hdN⟩,
      hdL, dvd_mul_right _ _⟩
  have hDS : D ⊆ S := fun d hd => hres d (hdata d hd).1 (hdata d hd).2.1
  have hcostD : mass D ≤ stepCost q := by
    unfold mass D
    rw [Finset.sum_image (fun _ _ _ _ e => hinj e)]
    exact hcost
  let w : ℕ := ∑ d ∈ D, L / d
  have hw : (w : ZMod p) = (m : ZMod p) := by
    change ((↑(∑ d ∈ D, L / d) : ZMod p)) = _
    rw [Nat.cast_sum, show D = C.image f from rfl, Finset.sum_image (fun _ _ _ _ e => hinj e)]
    calc
      (∑ c ∈ C, ((L / f c : ℕ) : ZMod p)) = ∑ c ∈ C, v * (c : ZMod p)⁻¹ := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (weight_mod hp (hC c hc).1 (hC c hc).2.1 (hC c hc).2.2).2
      _ = v * ((m : ZMod p) / v) := by rw [← Finset.mul_sum, hsumC]
      _ = (m : ZMod p) := by
        have hv' : v ≠ 0 := hv
        rw [mul_comm v, div_mul_cancel₀ _ hv']
  have hdiv : (p : ℤ) ∣ m - (w : ℤ) := by
    apply (CharP.intCast_eq_zero_iff (ZMod p) p _).1
    simp only [Int.cast_sub, Int.cast_natCast, hw, sub_self]
  obtain ⟨u, hu⟩ := hdiv
  let T := S \ D
  have hmT : mass T = mass S - mass D := mass_sdiff hDS
  have hmD : mass D = (w : ℚ) / (L : ℚ) := by
    apply (eq_div_iff (by exact_mod_cast hL : (L : ℚ) ≠ 0)).2
    have hscaled := scaled_mass (S := D) (L := L) fun d hd =>
      ⟨by have := (Finset.mem_Icc.1 (hdata d hd).1).1; omega, (hdata d hd).2.1⟩
    simpa [w, mul_comm] using hscaled
  have hTden : (mass T).den ∣ B := by
    apply den_from_fraction (m := u)
    have huQ : (m : ℚ) - (w : ℚ) = (p : ℚ) * (u : ℚ) := by exact_mod_cast hu
    rw [hmT, hm, hmD, ← sub_div, huQ, hLB, Nat.cast_mul]
    exact mul_div_mul_left _ _ (by exact_mod_cast hp.ne_zero : (p : ℚ) ≠ 0)
  refine ⟨T, Finset.sdiff_subset, hTden, ?_, by linarith⟩
  intro d hd hdB
  have hdS := hres d hd (hdB.trans (lcmUpto_mono (show q - 1 ≤ q by omega)))
  apply Finset.mem_sdiff.2 ⟨hdS, ?_⟩
  intro hdD
  have hdq := (hdata d hdD).2.2
  have hsmall : q ≤ q - 1 := (power_dvd_lcmUpto (by omega : 0 < q - 1) hp).1 (hdq.trans hdB)
  omega

theorem round_subsum (select : CofactorSelection) (N b : ℕ) (hb : 0 < b) (hNb : b^2 ≤ N)
    {S : Finset ℕ} (hden : (mass S).den ∣ Nat.lcmUpto b)
    (hres : ∀ d ∈ Icc 1 N, d ∣ Nat.lcmUpto b → d ∈ S) :
    ∃ T ⊆ S, (mass T).den = 1 ∧ mass S - mass T ≤ ∑ j ∈ Icc 2 b, stepCost j := by
  induction b using Nat.strong_induction_on generalizing S with
  | h b ih =>
    by_cases h1 : b = 1
    · subst b
      have hL : Nat.lcmUpto 1 = 1 := by simp [Nat.lcmUpto]
      rw [hL, Nat.dvd_one] at hden
      exact ⟨S, le_rfl, hden, by simp⟩
    have hb' : 2 ≤ b := by omega
    have hind : (b - 1) ^ 2 ≤ N := (Nat.pow_le_pow_left (by omega : b - 1 ≤ b) 2).trans hNb
    have step : ∃ V ⊆ S, (mass V).den ∣ Nat.lcmUpto (b - 1) ∧
        (∀ d ∈ Icc 1 N, d ∣ Nat.lcmUpto (b - 1) → d ∈ V) ∧ mass S - mass V ≤ stepCost b := by
      by_cases hpow : IsPrimePow b
      · obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff _).1 hpow
        exact cancellation_step select hp ha hNb hden hres
      · have hL := lcm_no_power hb' hpow
        rw [hL] at hden hres
        exact ⟨S, le_rfl, hden, hres, by simpa using cost_nonneg b⟩
    obtain ⟨V, hVS, hVden, hVres, hVcost⟩ := step
    obtain ⟨T, hTV, hTden, hTcost⟩ := ih (b - 1) (by omega) (by omega) hind hVden hVres
    refine ⟨T, hTV.trans hVS, hTden, ?_⟩
    have heq : Icc 2 b = insert b (Icc 2 (b - 1)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [heq, Finset.sum_insert (by simp [Finset.mem_Icc]; omega)]
    linarith

theorem integer_of_den_one {x : ℚ} (hx : 0 ≤ x) (hden : x.den = 1) : ∃ m : ℕ, x = m := by
  refine ⟨x.num.toNat, ?_⟩
  have hnum : 0 ≤ x.num := Rat.num_nonneg.2 hx
  calc
    x = (x.num : ℚ) / x.den := (x.num_div_den).symm
    _ = (x.num.toNat : ℚ) := by
      rw [hden, Nat.cast_one, div_one, ← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg hnum]

theorem all_heights (select : CofactorSelection)
    (cost_bound : ∀ b, (∑ j ∈ Icc 2 b, stepCost j) ≤ (4861 / 2520 + 3 / 5 : ℚ)) :
    ∀ N ≥ 1, ∃ m, Erdos308.representable N = Set.Icc 1 m := by
  have closed (N : ℕ) : 1 ≤ N → ClosedBelow N := by
    induction N with
    | zero => omega
    | succ n ih =>
      intro hn
      by_cases hs : n + 1 ≤ 64
      · exact closed_below_small hn hs
      have hn64 : 64 ≤ n := by omega
      have hnsqrt : 0 < n.sqrt := Nat.sqrt_pos.2 (by omega)
      obtain ⟨S, hS, hbest, hres⟩ := exists_best n
      obtain ⟨T, hT, h1, hcost⟩ := round_subsum select n n.sqrt hnsqrt (Nat.sqrt_le' n) hS.2 hres
      obtain ⟨z, hz⟩ := integer_of_den_one (mass_nonneg T) h1
      apply step_closed (by omega) (ih (by omega)) ⟨T, hT.trans hS.1, hz⟩
      intro k hk
      obtain ⟨V, hV, hk⟩ := hk
      have hV' : admissible (n + 1) V := by
        refine ⟨hV, ?_⟩
        rw [show mass V = (k : ℚ) from hk]
        simp
      obtain ⟨U, hU, hbound⟩ := change_height hn64 hV'
      have hle := cost_bound n.sqrt
      have hbestU := hbest U hU
      have hlt : (k : ℚ) < (z : ℚ) + 3 := by
        change mass V = (k : ℚ) at hk
        linarith
      have hk' : k < z + 3 := by exact_mod_cast hlt
      omega
  exact fun N hn => interval_of_closed (closed N hn)

end Erdos308AllHeights

namespace Erdos308Residues

private theorem pair {p : ℕ} [Fact p.Prime] (h : 10 < p) (r : ZMod p) :
    ∃ c d : ℕ, 0 < c ∧ c < p ∧ p ≤ 3*c ∧ 0 < d ∧ d < p ∧ p ≤ 3*d ∧
      c ≠ d ∧ (c : ZMod p)⁻¹ + (d : ZMod p)⁻¹ = r := by
  classical
  let I := Finset.Ico ((p+2)/3) p
  let f := fun c : ℕ => (c : ZMod p)⁻¹
  let A := I.image f
  let B := A.image (fun x => r-x)
  have hA : A.card = p - ((p+2)/3) := by
    change (I.image f).card = _
    rw [Finset.card_image_of_injOn]
    · exact Nat.card_Ico _ _
    · intro i hi j hj hij
      have e : (i : ZMod p) = j := inv_injective hij
      have v := congrArg ZMod.val e
      simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_Ico.mp hi).2,
        Nat.mod_eq_of_lt (Finset.mem_Ico.mp hj).2] using v
  have hB : B.card = A.card := Finset.card_image_of_injective _ (fun _ _ e => sub_right_injective e)
  have hu := Finset.card_le_univ (A ∪ B)
  rw [ZMod.card] at hu
  have hi := Finset.card_inter_add_card_union A B
  have hs : 1 < (A ∩ B).card := by omega
  have ht : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  obtain ⟨x, hx, hfix⟩ : ∃ x ∈ A ∩ B, x ≠ r/2 := by
    by_contra! hh
    have he := Finset.card_le_one.mpr (fun i hi j hj => (hh i hi).trans (hh j hj).symm)
    omega
  obtain ⟨hxA,hxB⟩ := Finset.mem_inter.mp hx
  obtain ⟨c,hc,ec⟩ := Finset.mem_image.mp hxA
  obtain ⟨y,hy,ey⟩ := Finset.mem_image.mp hxB
  obtain ⟨d,hd,ed⟩ := Finset.mem_image.mp hy
  obtain ⟨hc₁,hc₂⟩ := Finset.mem_Ico.mp hc
  obtain ⟨hd₁,hd₂⟩ := Finset.mem_Ico.mp hd
  refine ⟨c,d,by omega,hc₂,by omega,by omega,hd₂,by omega,?_,?_⟩
  · intro e
    subst d
    have : x = y := ec.symm.trans ed
    apply hfix
    apply (eq_div_iff ht).2
    linear_combination -ey + this
  · change f c + f d = r
    rw [ec,ed,← ey]
    abel

private theorem unit_bound {q c k : ℕ} (hq : 0 < q) (hc : 0 < c) (hk : q ≤ k*c) :
    (1 : ℚ) / ((q*c : ℕ) : ℚ) ≤ (k : ℚ) / (q : ℚ)^2 := by
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h : (q : ℚ) ≤ (k : ℚ)*c := by exact_mod_cast hk
  nlinarith [mul_le_mul_of_nonneg_left h (show (0:ℚ) ≤ q by positivity)]

theorem select_cofactors {p a : ℕ} (hp : p.Prime) (ha : 0 < a) [Fact p.Prime] (r : ZMod p) :
    ∃ C : Finset ℕ, (∀ c ∈ C, 0 < c ∧ c < p^a ∧ ¬ p ∣ c) ∧
      (∑ c ∈ C, (c : ZMod p)⁻¹) = r ∧
      (∑ c ∈ C, (1 : ℚ) / ((p^a*c : ℕ) : ℚ)) ≤
        (if p^a ≤ 10 then (1:ℚ)/(p^a:ℕ) else 6 / ((p^a:ℕ):ℚ)^2) := by
  classical
  have hq := pow_pos hp.pos a
  by_cases hr : r = 0
  · refine ⟨∅, by simp, by simp [hr], ?_⟩
    simp only [Finset.sum_empty]
    split <;> positivity
  let v := r⁻¹.val
  have hv : (v : ZMod p) = r⁻¹ := ZMod.natCast_zmod_val _
  have hvp : v < p := ZMod.val_lt _
  have hv₀ : 0 < v := by
    by_contra! e
    have he : v = 0 := by omega
    simp [he] at hv
    exact hr hv.symm
  have hvn := Nat.not_dvd_of_pos_of_lt hv₀ hvp
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have hpow : p^(b+1) = p^b*p := pow_succ _ _
  have hbpos := pow_pos hp.pos b
  by_cases hs : p^(b+1) ≤ 10
  · refine ⟨{v}, ?_, by simp [hv], ?_⟩
    · simpa using And.intro hv₀ (And.intro (show v < p^(b+1) by rw [hpow]; nlinarith) hvn)
    · simp only [Finset.sum_singleton, if_pos hs, Nat.cast_mul]
      apply one_div_le_one_div_of_le (by positivity)
      have hh : (1:ℚ) ≤ v := by exact_mod_cast hv₀
      nlinarith [mul_le_mul_of_nonneg_left hh (show (0:ℚ) ≤ (p^(b+1):ℕ) by positivity)]
  rw [if_neg hs]
  by_cases hb : b = 0
  · subst b
    simp only [zero_add, pow_one] at hs ⊢
    obtain ⟨c,d,hc,hl,hc₃,hd,hm,hd₃,hcd,he⟩ := pair (by omega : 10 < p) r
    refine ⟨{c,d}, ?_, by simpa [hcd] using he, ?_⟩
    · simp [hc,hd,hl,hm,Nat.not_dvd_of_pos_of_lt hc hl,Nat.not_dvd_of_pos_of_lt hd hm]
    · simp only [Finset.mem_singleton, hcd, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
      calc
        _ ≤ (3:ℚ)/(p:ℚ)^2 + 3/(p:ℚ)^2 := add_le_add (unit_bound hp.pos hc hc₃) (unit_bound hp.pos hd hd₃)
        _ = _ := by rw [← add_div]; norm_num
  · let c := (p^b-1)*p+v
    have hp₁ := hp.two_le
    have hp₂ : 2 ≤ p^b := by
      have h := Nat.pow_le_pow_right hp.pos (show 1 ≤ b by omega)
      simpa using (hp₁.trans (by simpa using h) : 2 ≤ p^b)
    have hsplit : (p^b-1)*p+p = p^(b+1) := by
      rw [hpow, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_one_add_one_eq_of_pos hbpos]
    have hc : 0 < c := by dsimp [c]; omega
    have hl : c < p^(b+1) := by dsimp [c]; omega
    have hcast : (c : ZMod p) = r⁻¹ := by simp [c,hv]
    have hdvd : ¬ p ∣ c := by
      rw [← ZMod.natCast_eq_zero_iff, hcast]
      exact inv_ne_zero hr
    refine ⟨{c}, by simp [hc,hl,hdvd], by simp [hcast], ?_⟩
    simp only [Finset.sum_singleton]
    apply unit_bound hq hc (k := 6)
    dsimp [c]
    have hm := Nat.mul_le_mul_right p (show 1 ≤ p^b-1 by omega)
    simp only [one_mul] at hm
    omega

end Erdos308Residues

theorem OMA.solution : type_of% @Erdos308.erdos_308.variants.all_N := by
  apply Erdos308AllHeights.all_heights
  · intro p a _ hp ha r
    simpa [Erdos308AllHeights.stepCost] using Erdos308Residues.select_cofactors hp ha r
  · intro b
    simpa [Erdos308AllHeights.stepCost] using Erdos308AllHeights.sum_cost_le b
