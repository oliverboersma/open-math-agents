import FormalConjectures.ErdosProblems.«731»

/-! Proof of Erdos731.erdos_731.variants.egrs75 (Erdos-Graham-Ruzsa-Straus 1975). -/

open Filter Real
open scoped Topology

namespace OMA.Erdos731

private def basePDigit (p n j : ℕ) : ℕ :=
  (n / p ^ j) % p

private def highDigitCount (p r n : ℕ) : ℕ :=
  ((Finset.range r).filter (fun j => p ≤ 2 * basePDigit p n j)).card

private lemma centralBinom_mul_sq_factorial (n : ℕ) :
    n.centralBinom * (Nat.factorial n * Nat.factorial n) = Nat.factorial (2 * n) := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h := Nat.choose_mul_factorial_mul_factorial (by omega : n ≤ 2 * n)
  have hsub : 2 * n - n = n := by omega
  rwa [hsub, mul_assoc] at h

private lemma two_mul_div_le (n m : ℕ) : 2 * (n / m) ≤ 2 * n / m := by
  by_cases hm : m = 0
  · subst hm; simp
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
    rw [Nat.le_div_iff_mul_le hm_pos]
    calc 2 * (n / m) * m = 2 * (n / m * m) := by ring
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self n m)

private lemma padicValNat_centralBinom {p n b : ℕ} [Fact p.Prime] (hb : Nat.log p (2 * n) < b) :
    padicValNat p n.centralBinom =
      ∑ j ∈ Finset.Ico 1 b, (2 * n / p ^ j - 2 * (n / p ^ j)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hlog_n : Nat.log p n < b :=
    lt_of_le_of_lt (Nat.log_mono_right (by omega : n ≤ 2 * n)) hb
  have hcb_ne : n.centralBinom ≠ 0 := n.centralBinom_pos.ne'
  have hfac_ne : Nat.factorial n ≠ 0 := Nat.factorial_ne_zero n
  have hmul_eq := centralBinom_mul_sq_factorial n
  have hpadic : padicValNat p (Nat.factorial (2 * n)) =
      padicValNat p n.centralBinom + 2 * padicValNat p (Nat.factorial n) := by
    rw [← hmul_eq, padicValNat.mul hcb_ne (mul_ne_zero hfac_ne hfac_ne),
      padicValNat.mul hfac_ne hfac_ne]
    ring
  rw [padicValNat_factorial hb, padicValNat_factorial hlog_n] at hpadic
  have hsum_add :
      (∑ j ∈ Finset.Ico 1 b, (2 * n / p ^ j - 2 * (n / p ^ j))) +
        2 * ∑ j ∈ Finset.Ico 1 b, n / p ^ j =
      ∑ j ∈ Finset.Ico 1 b, (2 * n / p ^ j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Nat.sub_add_cancel (two_mul_div_le n (p ^ j))
  omega

private lemma highDigitCarry {p n j : ℕ} (hp : 0 < p) (hj : p ≤ 2 * basePDigit p n j) :
    1 ≤ 2 * n / p ^ (j + 1) - 2 * (n / p ^ (j + 1)) := by
  have hpj_pos : 0 < p ^ j := pow_pos hp j
  have hpow : p ^ (j + 1) = p ^ j * p := pow_succ p j
  set m := n / p ^ j
  have hdiv_mod : m = p * (m / p) + m % p := (Nat.div_add_mod m p).symm
  have hq : m / p = n / p ^ (j + 1) := by
    dsimp [m]
    rw [Nat.div_div_eq_div_mul, ← hpow]
  have hd : m % p = basePDigit p n j := rfl
  have hn_eq : n = p ^ j * m + n % p ^ j := (Nat.div_add_mod n (p ^ j)).symm
  have h2n_ge : p ^ (j + 1) * (2 * (n / p ^ (j + 1)) + 1) ≤ 2 * n := by
    calc p ^ (j + 1) * (2 * (n / p ^ (j + 1)) + 1)
        = p ^ (j + 1) * (2 * (m / p)) + p ^ j * p := by rw [hq, hpow]; ring
      _ ≤ p ^ (j + 1) * (2 * (m / p)) + p ^ j * (2 * (m % p)) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left (p ^ j) hj) _
      _ = 2 * (p ^ j * (p * (m / p) + m % p)) := by rw [hpow]; ring
      _ = 2 * (p ^ j * m) := by rw [← hdiv_mod]
      _ ≤ 2 * (p ^ j * m + n % p ^ j) := Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)
      _ = 2 * n := by rw [← hn_eq]
  have hpj1_pos : 0 < p ^ (j + 1) := pow_pos hp (j + 1)
  have hle : 2 * (n / p ^ (j + 1)) + 1 ≤ 2 * n / p ^ (j + 1) :=
    (Nat.le_div_iff_mul_le hpj1_pos).mpr (by rw [mul_comm]; exact h2n_ge)
  omega

private lemma highDigitCount_le_padicValNat {p r n : ℕ} [Fact p.Prime] :
    highDigitCount p r n ≤ padicValNat p n.centralBinom := by
  let b := max r (Nat.log p (2 * n)) + 2
  have hb : Nat.log p (2 * n) < b := by dsimp [b]; omega
  rw [padicValNat_centralBinom hb]
  let S := (Finset.range r).filter (fun j => p ≤ 2 * basePDigit p n j)
  have hcard_eq : highDigitCount p r n = ∑ _j ∈ S, 1 := by
    simp [highDigitCount, S]
  rw [hcard_eq]
  have hsum_le : ∑ j ∈ S, 1 ≤ ∑ j ∈ S, (2 * n / p ^ (j + 1) - 2 * (n / p ^ (j + 1))) := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_filter] at hj
    exact highDigitCarry (Fact.out : p.Prime).pos hj.2
  refine hsum_le.trans ?_
  have hsum_img : ∑ j ∈ S, (2 * n / p ^ (j + 1) - 2 * (n / p ^ (j + 1))) =
      ∑ k ∈ S.image (fun j => j + 1), (2 * n / p ^ k - 2 * (n / p ^ k)) := by
    rw [Finset.sum_image]
    intro x _ y _ h
    dsimp at h
    omega
  rw [hsum_img]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => Nat.zero_le _)
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
  rw [Finset.mem_filter, Finset.mem_range] at hj
  rw [Finset.mem_Ico]
  have hrb : r + 1 ≤ b := by dsimp [b]; omega
  exact ⟨Nat.succ_pos j, Nat.lt_of_lt_of_le (Nat.succ_lt_succ hj.1) hrb⟩

private lemma two_mul_mod_lt {p r n : ℕ} (hp : 0 < p)
    (hdig : ∀ j ∈ Finset.range (r - 1), 2 * basePDigit p n j < p) :
    ∀ k ≤ r - 1, 2 * (n % p ^ k) < p ^ k := by
  intro k hk
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    have hk_lt : k < r - 1 := by omega
    have ihk : 2 * (n % p ^ k) < p ^ k := ih hk_lt.le
    have hdk : 2 * basePDigit p n k < p := hdig k (Finset.mem_range.mpr hk_lt)
    have hmod_eq : n % p ^ (k + 1) = basePDigit p n k * p ^ k + n % p ^ k := by
      have h1 : n = p ^ k * (n / p ^ k) + n % p ^ k := (Nat.div_add_mod n (p ^ k)).symm
      have h2 : n / p ^ k = p * ((n / p ^ k) / p) + basePDigit p n k :=
        (Nat.div_add_mod (n / p ^ k) p).symm
      have h3 : n = p ^ (k + 1) * ((n / p ^ k) / p) + (basePDigit p n k * p ^ k + n % p ^ k) := by
        calc n = p ^ k * (n / p ^ k) + n % p ^ k := h1
          _ = p ^ k * (p * ((n / p ^ k) / p) + basePDigit p n k) + n % p ^ k := by
              conv_lhs => rw [h2]
          _ = (p ^ k * p) * ((n / p ^ k) / p) + (basePDigit p n k * p ^ k + n % p ^ k) := by ring
          _ = p ^ (k + 1) * ((n / p ^ k) / p) + (basePDigit p n k * p ^ k + n % p ^ k) := by
              rw [pow_succ]
      have hlt_pow : basePDigit p n k * p ^ k + n % p ^ k < p ^ (k + 1) := by
        have hpj_pos : 0 < p ^ k := pow_pos hp k
        have hdm : basePDigit p n k ≤ p - 1 := by
          have : basePDigit p n k < p := Nat.mod_lt _ hp
          omega
        calc basePDigit p n k * p ^ k + n % p ^ k
            ≤ (p - 1) * p ^ k + (p ^ k - 1) := by
              have hrem : n % p ^ k < p ^ k := Nat.mod_lt _ hpj_pos
              exact Nat.add_le_add (Nat.mul_le_mul_right _ hdm) (by omega)
          _ < p * p ^ k := by
              have hmul : (p - 1) * p ^ k + p ^ k = p * p ^ k := by
                have := Nat.sub_add_cancel hp
                calc (p - 1) * p ^ k + p ^ k = ((p - 1) + 1) * p ^ k := by ring
                  _ = p * p ^ k := by rw [this]
              omega
          _ = p ^ (k + 1) := by rw [pow_succ']
      conv_lhs => rw [h3, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hlt_pow]
    have hdk_le : 2 * basePDigit p n k ≤ p - 1 := by omega
    have hmul_le : 2 * basePDigit p n k * p ^ k ≤ (p - 1) * p ^ k :=
      Nat.mul_le_mul_right _ hdk_le
    calc 2 * (n % p ^ (k + 1))
        = 2 * basePDigit p n k * p ^ k + 2 * (n % p ^ k) := by rw [hmod_eq]; ring
      _ < (p - 1) * p ^ k + p ^ k := by omega
      _ = p * p ^ k := by
          have := Nat.sub_add_cancel hp
          calc (p - 1) * p ^ k + p ^ k = ((p - 1) + 1) * p ^ k := by ring
            _ = p * p ^ k := by rw [this]
      _ = p ^ (k + 1) := by rw [pow_succ']

private lemma fract_div_pow_lt_half {p r n k : ℕ} (hp : 0 < p) (hk : k ≤ r - 1)
    (hdig : ∀ j ∈ Finset.range (r - 1), 2 * basePDigit p n j < p) :
    Int.fract ((n : ℝ) / p ^ k) < 1 / 2 := by
  have hmod : 2 * (n % p ^ k) < p ^ k := two_mul_mod_lt hp hdig k hk
  have hp_pos : (0 : ℝ) < (p : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hp) k
  have hmod_real : ((n % p ^ k : ℕ) : ℝ) / (p : ℝ) ^ k < 1 / 2 := by
    rw [div_lt_div_iff₀ hp_pos (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (by linarith : (n % p ^ k) * 2 < 1 * p ^ k)
  have hn_eq : (n : ℝ) / (p : ℝ) ^ k = ((n / p ^ k : ℕ) : ℝ) + ((n % p ^ k : ℕ) : ℝ) / (p : ℝ) ^ k := by
    have hnat : n = p ^ k * (n / p ^ k) + n % p ^ k := (Nat.div_add_mod n (p ^ k)).symm
    have hreal : (n : ℝ) = (p : ℝ) ^ k * ((n / p ^ k : ℕ) : ℝ) + ((n % p ^ k : ℕ) : ℝ) := by
      exact_mod_cast hnat
    rw [hreal]
    field_simp [hp_pos.ne']
  rw [hn_eq, Int.fract_natCast_add]
  have hnn : 0 ≤ ((n % p ^ k : ℕ) : ℝ) / (p : ℝ) ^ k := by
    exact div_nonneg (Nat.cast_nonneg _) hp_pos.le
  rw [Int.fract_eq_self.mpr ⟨hnn, hmod_real.trans (by norm_num)⟩]
  exact hmod_real

private lemma not_dvd_centralBinom_of_small_digits {p r n : ℕ} (hp : p.Prime)
    (hn : 2 * n < p ^ r) (hdig : ∀ j ∈ Finset.range (r - 1), 2 * basePDigit p n j < p) :
    ¬ p ∣ n.centralBinom := by
  let : Fact p.Prime := ⟨hp⟩
  have hb : Nat.log p (2 * n) < r + 1 := by
    by_cases hn0 : n = 0
    · simp [hn0]
    · exact lt_of_lt_of_le (Nat.log_lt_of_lt_pow (by omega) hn) (Nat.le_succ r)
  have hpadic := padicValNat_centralBinom (p := p) (n := n) (b := r + 1) hb
  have hzero : padicValNat p n.centralBinom = 0 := by
    rw [hpadic]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    rcases eq_or_lt_of_le (show k ≤ r by omega) with rfl | hkr
    · have h1 : 2 * n / p ^ k = 0 := Nat.div_eq_of_lt hn
      have h2 : n / p ^ k = 0 := Nat.div_eq_of_lt (by omega)
      simp [h1, h2]
    · have hk_le : k ≤ r - 1 := by omega
      have hmod := two_mul_mod_lt hp.pos hdig k hk_le
      have h2n_eq : 2 * n = p ^ k * (2 * (n / p ^ k)) + 2 * (n % p ^ k) := by
        have h1 : n = p ^ k * (n / p ^ k) + n % p ^ k := (Nat.div_add_mod n (p ^ k)).symm
        linarith
      have hdiv_eq : 2 * n / p ^ k = 2 * (n / p ^ k) := by
        rw [h2n_eq, Nat.mul_add_div (pow_pos hp.pos k), Nat.div_eq_of_lt hmod, add_zero]
      rw [hdiv_eq, Nat.sub_self]
  intro hdvd
  have h1 : 1 ≤ padicValNat p n.centralBinom :=
    (padicValNat_dvd_iff_le n.centralBinom_pos.ne').mp (by simpa using hdvd)
  omega

private lemma sum_digits_factor (p : ℕ) (hp : 0 < p) :
    ∑ d ∈ Finset.range p, (if p ≤ 2 * d then (1 / 2 : ℝ) else 1) =
      ((p + (p + 1) / 2 : ℕ) : ℝ) / 2 := by
  let k := (p + 1) / 2
  have hk_le : k ≤ p := by dsimp [k]; omega
  have hsplit : Finset.range p = Finset.range k ∪ Finset.Ico k p := by
    ext d
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range k) (Finset.Ico k p) := by
    rw [Finset.disjoint_left]
    intro d hd1 hd2
    simp only [Finset.mem_range, Finset.mem_Ico] at hd1 hd2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hsum1 : ∑ d ∈ Finset.range k, (if p ≤ 2 * d then (1 / 2 : ℝ) else 1) = (k : ℝ) := by
    have hcongr : ∑ d ∈ Finset.range k, (if p ≤ 2 * d then (1 / 2 : ℝ) else 1) =
        ∑ _d ∈ Finset.range k, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_range] at hd
      rw [if_neg (by dsimp [k] at hd; omega)]
    rw [hcongr]
    simp
  have hsum2 : ∑ d ∈ Finset.Ico k p, (if p ≤ 2 * d then (1 / 2 : ℝ) else 1) =
      ((p - k : ℕ) : ℝ) * (1 / 2) := by
    have hcongr : ∑ d ∈ Finset.Ico k p, (if p ≤ 2 * d then (1 / 2 : ℝ) else 1) =
        ∑ _d ∈ Finset.Ico k p, (1 / 2 : ℝ) := by
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_Ico] at hd
      rw [if_pos (by dsimp [k] at hd; omega)]
    rw [hcongr]
    simp
  rw [hsum1, hsum2, Nat.cast_add, Nat.cast_sub hk_le]
  ring

private lemma highDigitCount_step {p r q d : ℕ} (hp : 0 < p) (hd : d < p) :
    highDigitCount p (r + 1) (q * p + d) =
      highDigitCount p r q + (if p ≤ 2 * d then 1 else 0) := by
  have hsplit : Finset.range (r + 1) = insert 0 ((Finset.range r).image (· + 1)) := by
    ext j
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact Or.inl rfl
      · exact Or.inr ⟨j - 1, by omega, by omega⟩
    · rintro (rfl | ⟨k, hk, rfl⟩) <;> omega
  have hnot0 : 0 ∉ (Finset.range r).image (· + 1) := by simp
  have hf_zero : basePDigit p (q * p + d) 0 = d := by
    dsimp [basePDigit]
    rw [Nat.div_one, mul_comm q p, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hd]
  have hf_succ : ∀ j : ℕ, basePDigit p (q * p + d) (j + 1) = basePDigit p q j := by
    intro j
    dsimp [basePDigit]
    rw [pow_succ', ← Nat.div_div_eq_div_mul, mul_comm q p, Nat.mul_add_div hp,
      Nat.div_eq_of_lt hd, add_zero]
  dsimp [highDigitCount]
  rw [hsplit, Finset.filter_insert]
  have hf_img : ((Finset.range r).image (· + 1)).filter (fun j => p ≤ 2 * basePDigit p (q * p + d) j) =
      ((Finset.range r).filter (fun j => p ≤ 2 * basePDigit p q j)).image (· + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, hcond⟩
      rw [hf_succ] at hcond
      exact ⟨j, ⟨hj, hcond⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hcond⟩, rfl⟩
      exact ⟨⟨j, hj, rfl⟩, by rw [hf_succ]; exact hcond⟩
  rw [hf_zero]
  split_ifs with h0
  · rw [Finset.card_insert_of_notMem, hf_img, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
    intro hmem
    rw [hf_img] at hmem
    simp at hmem
  · rw [hf_img, Finset.card_image_of_injective _ (fun _ _ h => by omega), add_zero]

private lemma sum_two_pow_neg_highDigitCount (p r : ℕ) (hp : 0 < p) :
    ∑ n ∈ Finset.range (p ^ r), (2 : ℝ) ^ (-(highDigitCount p r n : ℤ)) =
      (((p + (p + 1) / 2 : ℕ) : ℝ) / 2) ^ r := by
  induction r with
  | zero => simp [highDigitCount]
  | succ r ih =>
    have hbij : ∑ n ∈ Finset.range (p ^ (r + 1)), (2 : ℝ) ^ (-(highDigitCount p (r + 1) n : ℤ)) =
        ∑ q ∈ Finset.range (p ^ r), ∑ d ∈ Finset.range p,
          (2 : ℝ) ^ (-(highDigitCount p (r + 1) (q * p + d) : ℤ)) := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun n _ => (n / p, n % p)) ?_ ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_range] at hn
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        have : n / p < p ^ r := Nat.div_lt_of_lt_mul (by rwa [pow_succ'] at hn)
        exact ⟨this, Nat.mod_lt n hp⟩
      · intro a _ b _ hab
        have h1 : a / p = b / p := congrArg Prod.fst hab
        have h2 : a % p = b % p := congrArg Prod.snd hab
        have ha : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
        have hb : b = p * (b / p) + b % p := (Nat.div_add_mod b p).symm
        rw [← h1, ← h2] at hb
        exact ha.trans hb.symm
      · rintro ⟨q, d⟩ hqd
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hqd
        refine ⟨q * p + d, Finset.mem_range.mpr ?_, ?_⟩
        · rw [pow_succ]
          have h1 : q + 1 ≤ p ^ r := hqd.1
          have h2 : (q + 1) * p ≤ p ^ r * p := Nat.mul_le_mul_right p h1
          have h3 : q * p + d < (q + 1) * p := by rw [Nat.succ_mul]; omega
          exact lt_of_lt_of_le h3 h2
        · ext
          · dsimp
            rw [mul_comm q p, Nat.mul_add_div hp, Nat.div_eq_of_lt hqd.2, add_zero]
          · dsimp
            rw [mul_comm q p, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hqd.2]
      · intro n _
        dsimp
        rw [mul_comm (n / p) p, Nat.div_add_mod]
    rw [hbij]
    have hsplit : ∑ q ∈ Finset.range (p ^ r), ∑ d ∈ Finset.range p,
        (2 : ℝ) ^ (-(highDigitCount p (r + 1) (q * p + d) : ℤ)) =
        (∑ q ∈ Finset.range (p ^ r), (2 : ℝ) ^ (-(highDigitCount p r q : ℤ))) *
          ∑ d ∈ Finset.range p, (if p ≤ 2 * d then (1 / 2 : ℝ) else 1) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_range] at hd
      rw [highDigitCount_step hp hd]
      split_ifs with h0
      · have hexp : -(highDigitCount p r q + 1 : ℤ) = -(highDigitCount p r q : ℤ) + (-1 : ℤ) := by
          omega
        push_cast
        rw [hexp, zpow_add₀ (by norm_num)]
        norm_num
      · simp
    rw [hsplit, ih, sum_digits_factor p hp, pow_succ]

private lemma prime_ratio_le_five_sixths {p : ℕ} (hp : 2 ≤ p) :
    ((p + (p + 1) / 2 : ℕ) : ℝ) / (2 * p) ≤ 5 / 6 := by
  have hp_pos : (0 : ℝ) < 2 * p := by positivity
  rw [div_le_div_iff₀ hp_pos (by norm_num : (0 : ℝ) < 6)]
  norm_cast
  omega

private lemma highDigitCount_mod_pow {p r n : ℕ} (hp : 0 < p) :
    highDigitCount p r (n % p ^ r) = highDigitCount p r n := by
  dsimp [highDigitCount]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  refine and_congr_right fun hj => ?_
  have hr : r = j + (r - j) := by omega
  have h1 : p ^ r = p ^ j * p ^ (r - j) := by rw [← pow_add, ← hr]
  have hpj_pos : 0 < p ^ j := pow_pos hp j
  have hp_dvd : p ∣ p ^ (r - j) := dvd_pow_self p (by omega)
  rcases hp_dvd with ⟨t, ht⟩
  have hmod_eq : n = p ^ j * (p * t * (n / p ^ r)) + n % p ^ r := by
    have h := (Nat.div_add_mod n (p ^ r)).symm
    have hr_eq : p ^ r = p ^ j * (p * t) := h1.trans (by rw [ht])
    calc n = p ^ r * (n / p ^ r) + n % p ^ r := h
      _ = p ^ j * (p * t * (n / p ^ r)) + n % p ^ r := by rw [hr_eq]; ring
  have hdiv : n / p ^ j = p * (t * (n / p ^ r)) + (n % p ^ r) / p ^ j := by
    nth_rw 1 [hmod_eq]
    rw [Nat.mul_add_div hpj_pos]
    ring_nf
  dsimp [basePDigit]
  rw [hdiv, Nat.mul_add_mod_self_left]

private lemma card_not_dvd_prime_pow_le {p a r X : ℕ} (hp : p.Prime)
    (hpr : p ^ r ≤ X) :
    (((Finset.range X).filter (fun n => ¬ p ^ a ∣ n.centralBinom)).card : ℝ) ≤
      2 * (2 : ℝ) ^ a * (5 / 6 : ℝ) ^ r * X := by
  let : Fact p.Prime := ⟨hp⟩
  let P := p ^ r
  have hP_pos : 0 < P := pow_pos hp.pos r
  let K := X / P + 1
  have hXK : X ≤ K * P := by
    have h1 : X = P * (X / P) + X % P := (Nat.div_add_mod X P).symm
    have h2 : X % P < P := Nat.mod_lt X hP_pos
    dsimp [K]
    nlinarith
  have hKX : (K * P : ℝ) ≤ 2 * X := by
    have h1 : 1 ≤ X / P := (Nat.le_div_iff_mul_le hP_pos).mpr (by simpa using hpr)
    have h2 : K ≤ 2 * (X / P) := by dsimp [K]; omega
    have h3 : K * P ≤ 2 * (P * (X / P)) := by nlinarith
    have h4 : P * (X / P) ≤ X := Nat.mul_div_le X P
    exact_mod_cast h3.trans (by omega)
  let F := (Finset.range X).filter (fun n => ¬ p ^ a ∣ n.centralBinom)
  have hF_le : (F.card : ℝ) * (2 : ℝ) ^ (-(a : ℤ)) ≤
      ∑ n ∈ Finset.range (K * P), (2 : ℝ) ^ (-(highDigitCount p r n : ℤ)) := by
    have h1 : (F.card : ℝ) * (2 : ℝ) ^ (-(a : ℤ)) = ∑ _n ∈ F, (2 : ℝ) ^ (-(a : ℤ)) := by
      simp [mul_comm]
    have h2 : ∑ _n ∈ F, (2 : ℝ) ^ (-(a : ℤ)) ≤
        ∑ n ∈ F, (2 : ℝ) ^ (-(highDigitCount p r n : ℤ)) := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [Finset.mem_filter] at hn
      have hpad : padicValNat p n.centralBinom < a := by
        by_contra hge
        have hge' : a ≤ padicValNat p n.centralBinom := by omega
        exact hn.2 ((padicValNat_dvd_iff_le n.centralBinom_pos.ne').mpr hge')
      have hcnt : highDigitCount p r n ≤ a :=
        (highDigitCount_le_padicValNat).trans hpad.le
      have hexp : -(a : ℤ) ≤ -(highDigitCount p r n : ℤ) := by omega
      exact zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
    have hF_sub : F ⊆ Finset.range (K * P) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range] at hn
      exact Finset.mem_range.mpr (lt_of_lt_of_le hn.1 hXK)
    have h3 : ∑ n ∈ F, (2 : ℝ) ^ (-(highDigitCount p r n : ℤ)) ≤
        ∑ n ∈ Finset.range (K * P), (2 : ℝ) ^ (-(highDigitCount p r n : ℤ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hF_sub fun _ _ _ => by positivity
    exact h1 ▸ h2.trans h3
  have hsum_KP : ∑ n ∈ Finset.range (K * P), (2 : ℝ) ^ (-(highDigitCount p r n : ℤ)) =
      (K : ℝ) * (((p + (p + 1) / 2 : ℕ) : ℝ) / 2) ^ r := by
    have hbij : ∑ n ∈ Finset.range (K * P), (2 : ℝ) ^ (-(highDigitCount p r n : ℤ)) =
        ∑ q ∈ Finset.range K, ∑ d ∈ Finset.range P,
          (2 : ℝ) ^ (-(highDigitCount p r (q * P + d) : ℤ)) := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun n _ => (n / P, n % P)) ?_ ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_range] at hn
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨Nat.div_lt_of_lt_mul (by linarith), Nat.mod_lt n hP_pos⟩
      · intro a _ b _ hab
        have h1 : a / P = b / P := congrArg Prod.fst hab
        have h2 : a % P = b % P := congrArg Prod.snd hab
        have ha : a = P * (a / P) + a % P := (Nat.div_add_mod a P).symm
        have hb : b = P * (b / P) + b % P := (Nat.div_add_mod b P).symm
        rw [← h1, ← h2] at hb
        exact ha.trans hb.symm
      · rintro ⟨q, d⟩ hqd
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hqd
        refine ⟨q * P + d, Finset.mem_range.mpr ?_, ?_⟩
        · have : q ≤ K - 1 := by omega
          nlinarith
        · ext
          · dsimp; rw [mul_comm q P, Nat.mul_add_div hP_pos, Nat.div_eq_of_lt hqd.2, add_zero]
          · dsimp; rw [mul_comm q P, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hqd.2]
      · intro n _
        dsimp
        rw [mul_comm (n / P) P, Nat.div_add_mod]
    rw [hbij]
    have hperiod : ∀ q d, d < P →
        highDigitCount p r (q * P + d) = highDigitCount p r d := by
      intro q d hd
      rw [← highDigitCount_mod_pow (p := p) (r := r) hp.pos (n := q * P + d)]
      congr 1
      dsimp [P]
      rw [mul_comm q (p ^ r), Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hd]
    have hconst : ∑ q ∈ Finset.range K, ∑ d ∈ Finset.range P,
        (2 : ℝ) ^ (-(highDigitCount p r (q * P + d) : ℤ)) =
        (K : ℝ) * ∑ d ∈ Finset.range P, (2 : ℝ) ^ (-(highDigitCount p r d : ℤ)) := by
      trans ∑ _q ∈ Finset.range K,
          ∑ d ∈ Finset.range P, (2 : ℝ) ^ (-(highDigitCount p r d : ℤ))
      · refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun d hd => ?_
        rw [Finset.mem_range] at hd
        rw [hperiod q d hd]
      · simp
    rw [hconst, sum_two_pow_neg_highDigitCount p r hp.pos]
  have hbound : (F.card : ℝ) * (2 : ℝ) ^ (-(a : ℤ)) ≤ 2 * (5 / 6 : ℝ) ^ r * X := by
    have h1 : (((p + (p + 1) / 2 : ℕ) : ℝ) / 2) ^ r ≤ (p : ℝ) ^ r * (5 / 6 : ℝ) ^ r := by
      have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
      have hr1 : (((p + (p + 1) / 2 : ℕ) : ℝ) / 2) ≤ (p : ℝ) * (5 / 6) := by
        have hle := prime_ratio_le_five_sixths hp.two_le
        calc (((p + (p + 1) / 2 : ℕ) : ℝ) / 2)
            = (p : ℝ) * (((p + (p + 1) / 2 : ℕ) : ℝ) / (2 * p)) := by
              field_simp [hp_pos.ne']
          _ ≤ (p : ℝ) * (5 / 6) := mul_le_mul_of_nonneg_left hle hp_pos.le
      calc (((p + (p + 1) / 2 : ℕ) : ℝ) / 2) ^ r
          ≤ ((p : ℝ) * (5 / 6)) ^ r := pow_le_pow_left₀ (by positivity) hr1 r
        _ = (p : ℝ) ^ r * (5 / 6 : ℝ) ^ r := mul_pow _ _ r
    calc (F.card : ℝ) * (2 : ℝ) ^ (-(a : ℤ))
        ≤ (K : ℝ) * (((p + (p + 1) / 2 : ℕ) : ℝ) / 2) ^ r := hsum_KP ▸ hF_le
      _ ≤ (K : ℝ) * ((p : ℝ) ^ r * (5 / 6 : ℝ) ^ r) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (K * P : ℝ) * (5 / 6 : ℝ) ^ r := by dsimp [P]; push_cast; ring
      _ ≤ (2 * X : ℝ) * (5 / 6 : ℝ) ^ r :=
          mul_le_mul_of_nonneg_right hKX (by positivity)
      _ = 2 * (5 / 6 : ℝ) ^ r * X := by ring
  have h2a_pos : (0 : ℝ) < (2 : ℝ) ^ a := by positivity
  calc (F.card : ℝ)
      = ((F.card : ℝ) * (2 : ℝ) ^ (-(a : ℤ))) * (2 : ℝ) ^ a := by
        rw [zpow_neg, zpow_natCast]
        field_simp [h2a_pos.ne']
    _ ≤ (2 * (5 / 6 : ℝ) ^ r * X) * (2 : ℝ) ^ a :=
        mul_le_mul_of_nonneg_right hbound h2a_pos.le
    _ = 2 * (2 : ℝ) ^ a * (5 / 6 : ℝ) ^ r * X := by ring

private lemma bad1_density_tendsto_zero (ε' : ℝ) (hε' : 0 < ε') (hε'1 : ε' ≤ 1 / 4) :
    Tendsto (fun X : ℕ =>
      (((Finset.range X).filter (fun n =>
        ∃ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (Real.log X ^ (1 / 2 - ε' / 2)))),
          ¬ m ∣ n.centralBinom)).card : ℝ) / X)
      atTop (𝓝 0) := by
  let M1 : ℕ → ℕ := fun X => Nat.floor (Real.exp (Real.log X ^ (1 / 2 - ε' / 2)))
  have hlog_top : Tendsto (fun X : ℕ => Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heps_top : Tendsto (fun X : ℕ => Real.log X ^ ε') atTop atTop :=
    (tendsto_rpow_atTop hε').comp hlog_top
  have hhalf_pos : 0 < 1 / 2 - ε' / 2 := by linarith
  have hhalf_top : Tendsto (fun X : ℕ => Real.log X ^ (1 / 2 - ε' / 2)) atTop atTop :=
    (tendsto_rpow_atTop hhalf_pos).comp hlog_top
  have hexp_neg_zero : Tendsto (fun X : ℕ => 2 * Real.exp (-Real.log X ^ (1 / 2 - ε' / 2))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun X : ℕ => Real.exp (-Real.log X ^ (1 / 2 - ε' / 2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hhalf_top)
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul h1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp_neg_zero
    (Eventually.of_forall fun X => by positivity) ?_
  have hev_log : ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log X := hlog_top.eventually_ge_atTop 2
  have hev_eps : ∀ᶠ X : ℕ in atTop, 40 ≤ Real.log X ^ ε' := heps_top.eventually_ge_atTop 40
  have hev_half : ∀ᶠ X : ℕ in atTop, 40 ≤ Real.log X ^ (1 / 2 - ε' / 2) :=
    hhalf_top.eventually_ge_atTop 40
  have hev_X : ∀ᶠ X : ℕ in atTop, 1 ≤ X := eventually_ge_atTop 1
  filter_upwards [hev_log, hev_eps, hev_half, hev_X] with X hlogX heps hehalf hX1
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr hX1
  have hlogX_pos : 0 < Real.log X := by linarith
  let badSet := (Finset.range X).filter (fun n =>
    ∃ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (Real.log X ^ (1 / 2 - ε' / 2)))), ¬ m ∣ n.centralBinom)
  let Q := (Finset.Icc 2 (M1 X)).filter IsPrimePow
  have hsub_union : badSet ⊆ Q.biUnion (fun q => (Finset.range X).filter (fun n => ¬ q ∣ n.centralBinom)) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rcases hn.2 with ⟨m, hm, hndvd⟩
    rw [Finset.mem_Icc] at hm
    have hm_ne : m ≠ 0 := by omega
    have hnot_fac : ¬ ∀ p ∈ m.primeFactors, m.factorization p ≤ (n.centralBinom).factorization p := by
      intro hle
      apply hndvd
      refine (Nat.factorization_le_iff_dvd hm_ne n.centralBinom_pos.ne').mp fun p => ?_
      by_cases hp : p ∈ m.primeFactors
      · exact hle p hp
      · have hnot_supp : p ∉ m.factorization.support := by
          simpa [Nat.support_factorization] using hp
        rw [Finsupp.notMem_support_iff.mp hnot_supp]
        exact Nat.zero_le _
    push Not at hnot_fac
    rcases hnot_fac with ⟨p, hp, hlt⟩
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have ha_pos : 1 ≤ m.factorization p := hp_prime.factorization_pos_of_dvd hm_ne (Nat.dvd_of_mem_primeFactors hp)
    let a := m.factorization p
    let q := p ^ a
    have hq_dvd_m : q ∣ m := Nat.ordProj_dvd m p
    have hq_ge2 : 2 ≤ q := le_trans hp_prime.two_le (Nat.le_self_pow (by omega) p)
    have hq_le : q ≤ M1 X := (Nat.le_of_dvd hm.1 hq_dvd_m).trans hm.2
    have hq_pp : IsPrimePow q := hp_prime.isPrimePow.pow (by omega)
    have hq_ndvd : ¬ q ∣ n.centralBinom := by
      intro hqdvd
      have := (Nat.Prime.pow_dvd_iff_le_factorization hp_prime n.centralBinom_pos.ne').mp hqdvd
      omega
    exact Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq_ge2, hq_le⟩, hq_pp⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn.1, hq_ndvd⟩⟩
  have hcard_union : (badSet.card : ℝ) ≤
      ∑ q ∈ Q, (((Finset.range X).filter (fun n => ¬ q ∣ n.centralBinom)).card : ℝ) := by
    have h1 : badSet.card ≤ (Q.biUnion (fun q => (Finset.range X).filter (fun n => ¬ q ∣ n.centralBinom))).card :=
      Finset.card_le_card hsub_union
    have h2 : (Q.biUnion (fun q => (Finset.range X).filter (fun n => ¬ q ∣ n.centralBinom))).card ≤
        ∑ q ∈ Q, ((Finset.range X).filter (fun n => ¬ q ∣ n.centralBinom)).card :=
      Finset.card_biUnion_le
    exact_mod_cast h1.trans h2
  have hterm : ∀ q ∈ Q,
      (((Finset.range X).filter (fun n => ¬ q ∣ n.centralBinom)).card : ℝ) ≤
        2 * Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) * X := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    rcases hq.2 with ⟨p, a, hp_prim, ha_pos, rfl⟩
    have hp : p.Prime := Nat.prime_iff.mpr hp_prim
    let r := Nat.log p X
    have hpr : p ^ r ≤ X := Nat.pow_log_le_self p (by omega)
    have hle := card_not_dvd_prime_pow_le (p := p) (a := a) (r := r) (X := X) hp hpr
    have hq_real_le : (p : ℝ) ^ a ≤ Real.exp (Real.log X ^ (1 / 2 - ε' / 2)) := by
      have h1 : ((p ^ a : ℕ) : ℝ) ≤ M1 X := by exact_mod_cast hq.1.2
      simpa using h1.trans (Nat.floor_le (Real.exp_pos _).le)
    have hp_real_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    have ha_logp : (a : ℝ) * Real.log p ≤ Real.log X ^ (1 / 2 - ε' / 2) := by
      have h1 : Real.log ((p : ℝ) ^ a) ≤ Real.log X ^ (1 / 2 - ε' / 2) := by
        simpa [Real.log_exp] using Real.log_le_log (pow_pos hp_real_pos a) hq_real_le
      rwa [Real.log_pow] at h1
    have hr_logp : Real.log X < ((r + 1 : ℕ) : ℝ) * Real.log p := by
      have h1 : (X : ℝ) < (p : ℝ) ^ (r + 1) := by
        exact_mod_cast Nat.lt_pow_succ_log_self hp.one_lt X
      have h2 := Real.log_lt_log hX_pos h1
      rwa [Real.log_pow] at h2
    have hmul_div : Real.log X ^ (1 / 2 + ε' / 2) * Real.log X ^ (1 / 2 - ε' / 2) = Real.log X := by
      rw [← Real.rpow_add hlogX_pos]
      norm_num
    have hmul_eps : Real.log X ^ ε' * Real.log X ^ (1 / 2 - ε' / 2) = Real.log X ^ (1 / 2 + ε' / 2) := by
      rw [← Real.rpow_add hlogX_pos]
      congr 1; ring
    have hr1_ge : (a : ℝ) * Real.log X ^ (1 / 2 + ε' / 2) ≤ ((r + 1 : ℕ) : ℝ) := by
      have ha_pos_r : (0 : ℝ) < a := Nat.cast_pos.mpr ha_pos
      have hdiv_le : Real.log X ^ (1 / 2 + ε' / 2) ≤ Real.log X / ((a : ℝ) * Real.log p) := by
        rw [le_div_iff₀ (mul_pos ha_pos_r hlogp_pos)]
        calc Real.log X ^ (1 / 2 + ε' / 2) * ((a : ℝ) * Real.log p)
            ≤ Real.log X ^ (1 / 2 + ε' / 2) * Real.log X ^ (1 / 2 - ε' / 2) :=
              mul_le_mul_of_nonneg_left ha_logp (by positivity)
          _ = Real.log X := hmul_div
      have hgt : Real.log X / Real.log p < ((r + 1 : ℕ) : ℝ) := (div_lt_iff₀ hlogp_pos).mpr hr_logp
      calc (a : ℝ) * Real.log X ^ (1 / 2 + ε' / 2)
          ≤ (a : ℝ) * (Real.log X / ((a : ℝ) * Real.log p)) :=
            mul_le_mul_of_nonneg_left hdiv_le ha_pos_r.le
        _ = Real.log X / Real.log p := by field_simp [ha_pos_r.ne', hlogp_pos.ne']
        _ ≤ ((r + 1 : ℕ) : ℝ) := hgt.le
    have ha1_r : (1 : ℝ) ≤ a := by exact_mod_cast ha_pos
    have hplus_ge40 : 40 * (a : ℝ) * Real.log X ^ (1 / 2 - ε' / 2) ≤ (a : ℝ) * Real.log X ^ (1 / 2 + ε' / 2) := by
      rw [← hmul_eps]
      calc 40 * (a : ℝ) * Real.log X ^ (1 / 2 - ε' / 2)
          ≤ Real.log X ^ ε' * (a : ℝ) * Real.log X ^ (1 / 2 - ε' / 2) := by
            have h40 : 40 * (a : ℝ) ≤ Real.log X ^ ε' * (a : ℝ) :=
              mul_le_mul_of_nonneg_right heps (by positivity)
            exact mul_le_mul_of_nonneg_right h40 (by positivity)
        _ = (a : ℝ) * (Real.log X ^ ε' * Real.log X ^ (1 / 2 - ε' / 2)) := by ring
    have hr_sub_ge : 10 * a ≤ r ∧
        12 * Real.log X ^ (1 / 2 - ε' / 2) ≤ ((r - 10 * a : ℕ) : ℝ) := by
      have hplus_1600 : 1600 * (a : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
        have h1 : 40 ≤ Real.log X ^ (1 / 2 - ε' / 2) := hehalf
        nlinarith
      have h10a_le : 10 * a ≤ r := by
        have : 1600 * a ≤ r + 1 := by exact_mod_cast hplus_1600
        omega
      refine ⟨h10a_le, ?_⟩
      have hr_cast : ((r - 10 * a : ℕ) : ℝ) = (r : ℝ) - 10 * a := by
        rw [Nat.cast_sub h10a_le]; push_cast; rfl
      rw [hr_cast]
      have ha_r_10 : 12 * Real.log X ^ (1 / 2 - ε' / 2) + 10 * (a : ℝ) + 1 ≤
          40 * (a : ℝ) * Real.log X ^ (1 / 2 - ε' / 2) := by
        have : 12 * Real.log X ^ (1 / 2 - ε' / 2) ≤ 12 * (a : ℝ) * Real.log X ^ (1 / 2 - ε' / 2) := by
          nlinarith
        have : 10 * (a : ℝ) + 1 ≤ 11 * (a : ℝ) := by linarith
        have : 11 * (a : ℝ) ≤ (a : ℝ) * Real.log X ^ (1 / 2 - ε' / 2) := by nlinarith
        nlinarith
      have hr_plus_cast : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; rfl
      linarith [hr1_ge, hplus_ge40, hr_plus_cast]
    have hsplit_pow : (2 : ℝ) ^ a * (5 / 6 : ℝ) ^ r =
        ((2 : ℝ) * (5 / 6 : ℝ) ^ 10) ^ a * (5 / 6 : ℝ) ^ (r - 10 * a) := by
      have hr_eq : r = 10 * a + (r - 10 * a) := (Nat.add_sub_cancel' hr_sub_ge.1).symm
      nth_rw 1 [hr_eq]
      rw [pow_add, mul_pow, pow_mul]
      ring
    have hsmall_base : ((2 : ℝ) * (5 / 6 : ℝ) ^ 10) ^ a ≤ 1 := by
      refine pow_le_one₀ (by positivity) (by norm_num)
    have hexp_bound : (5 / 6 : ℝ) ^ (r - 10 * a) ≤ Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) := by
      have h56 : (5 / 6 : ℝ) ≤ Real.exp (-1 / 6) := by
        have := Real.add_one_le_exp (-1 / 6 : ℝ)
        linarith
      have h1 : (5 / 6 : ℝ) ^ (r - 10 * a) ≤ (Real.exp (-1 / 6)) ^ (r - 10 * a) :=
        pow_le_pow_left₀ (by norm_num) h56 _
      rw [← Real.exp_nat_mul] at h1
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      linarith [hr_sub_ge.2]
    refine hle.trans ?_
    have hprod_le : ((2 : ℝ) * (5 / 6 : ℝ) ^ 10) ^ a * (5 / 6 : ℝ) ^ (r - 10 * a) ≤
        Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) := by
      calc ((2 : ℝ) * (5 / 6 : ℝ) ^ 10) ^ a * (5 / 6 : ℝ) ^ (r - 10 * a)
          ≤ 1 * Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) :=
            mul_le_mul hsmall_base hexp_bound (by positivity) (by norm_num)
        _ = Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) := one_mul _
    calc 2 * (2 : ℝ) ^ a * (5 / 6 : ℝ) ^ r * X
        = 2 * (((2 : ℝ) ^ a * (5 / 6 : ℝ) ^ r) * X) := by ring
      _ = 2 * ((((2 : ℝ) * (5 / 6 : ℝ) ^ 10) ^ a * (5 / 6 : ℝ) ^ (r - 10 * a)) * X) := by
          rw [hsplit_pow]
      _ ≤ 2 * (Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) * X) := by gcongr
      _ = 2 * Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) * X := by ring
  have hQ_card : (Q.card : ℝ) ≤ Real.exp (Real.log X ^ (1 / 2 - ε' / 2)) := by
    have h1 : Q.card ≤ M1 X :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    have h2 : (Q.card : ℝ) ≤ M1 X := by exact_mod_cast h1
    exact h2.trans (Nat.floor_le (Real.exp_pos _).le)
  have hbad_le : (badSet.card : ℝ) ≤
      2 * Real.exp (-Real.log X ^ (1 / 2 - ε' / 2)) * X := by
    calc (badSet.card : ℝ)
        ≤ ∑ q ∈ Q, (((Finset.range X).filter (fun n => ¬ q ∣ n.centralBinom)).card : ℝ) :=
          hcard_union
      _ ≤ ∑ _q ∈ Q, (2 * Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) * X) :=
          Finset.sum_le_sum hterm
      _ = (Q.card : ℝ) * (2 * Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) * X) := by
          simp
      _ ≤ Real.exp (Real.log X ^ (1 / 2 - ε' / 2)) *
            (2 * Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2)) * X) := by
          gcongr
      _ = 2 * (Real.exp (Real.log X ^ (1 / 2 - ε' / 2)) *
            Real.exp (-2 * Real.log X ^ (1 / 2 - ε' / 2))) * X := by ring
      _ = 2 * Real.exp (-Real.log X ^ (1 / 2 - ε' / 2)) * X := by
          rw [← Real.exp_add]
          congr 2; ring
  dsimp only [badSet] at hbad_le
  exact (div_le_iff₀ hX_pos).mpr hbad_le

/- ## Step 3: Chebyshev Prime Interval Bound and Fejer Majorant -/

private lemma four_pow_le_succ_mul_centralBinom (Y : ℕ) :
    4 ^ Y ≤ (2 * Y + 1) * Y.centralBinom := by
  have hsum : ∑ k ∈ Finset.range (2 * Y + 1), (2 * Y).choose k = 4 ^ Y := by
    rw [Nat.sum_range_choose (2 * Y), pow_mul]
    norm_num
  have hle : ∑ k ∈ Finset.range (2 * Y + 1), (2 * Y).choose k ≤
      ∑ _k ∈ Finset.range (2 * Y + 1), Y.centralBinom := by
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Nat.centralBinom_eq_two_mul_choose]
    simpa [Nat.mul_div_cancel_left Y (by norm_num : 0 < 2)] using Nat.choose_le_middle k (2 * Y)
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hle
  linarith

private lemma padicValNat_centralBinom_le_log {p Y : ℕ} [Fact p.Prime] (_hY : 1 ≤ Y) :
    padicValNat p Y.centralBinom ≤ Nat.log p (2 * Y) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  let b := Nat.log p (2 * Y) + 1
  rw [padicValNat_centralBinom (Nat.lt_succ_self (Nat.log p (2 * Y)))]
  have hterm : ∀ j ∈ Finset.Ico 1 b, 2 * Y / p ^ j - 2 * (Y / p ^ j) ≤ 1 := by
    intro j _
    have hpj_pos : 0 < p ^ j := pow_pos (Fact.out : p.Prime).pos j
    have hlt : 2 * Y < p ^ j * (2 * (Y / p ^ j) + 2) := by
      have h1 : Y < p ^ j * (Y / p ^ j + 1) := by
        have := (Nat.div_add_mod Y (p ^ j)).symm
        have := Nat.mod_lt Y hpj_pos
        nlinarith
      nlinarith
    have hdiv_lt : 2 * Y / p ^ j < 2 * (Y / p ^ j) + 2 :=
      Nat.div_lt_of_lt_mul (by linarith)
    omega
  refine (Finset.sum_le_sum hterm).trans ?_
  simp [b]

private lemma padicValNat_centralBinom_le_one_of_sqrt_lt {p Y : ℕ} [Fact p.Prime]
    (hY : 1 ≤ Y) (hp : Nat.sqrt (2 * Y) < p) :
    padicValNat p Y.centralBinom ≤ 1 := by
  refine (padicValNat_centralBinom_le_log hY).trans ?_
  have hp2 : 2 * Y < p ^ 2 := by
    have := Nat.lt_succ_sqrt (2 * Y)
    have h1 : Nat.sqrt (2 * Y) + 1 ≤ p := hp
    nlinarith
  have hlog : Nat.log p (2 * Y) < 2 := Nat.log_lt_of_lt_pow (by omega) hp2
  omega

private lemma padicValNat_centralBinom_eq_zero_of_mid {p Y : ℕ} [Fact p.Prime]
    (hY : 5 ≤ Y) (hp_lo : 2 * Y / 3 < p) (hp_hi : p ≤ Y) :
    padicValNat p Y.centralBinom = 0 := by
  have hp2 : 2 * Y < p ^ 2 := by
    have h1 : 3 * p > 2 * Y := by omega
    nlinarith
  have hlog : Nat.log p (2 * Y) < 2 := Nat.log_lt_of_lt_pow (by omega) hp2
  rw [padicValNat_centralBinom (b := 2) hlog]
  have hIco : Finset.Ico 1 2 = {1} := by decide
  rw [hIco, Finset.sum_singleton, pow_one]
  have h1 : Y / p = 1 := by
    have hlo : 1 ≤ Y / p := (Nat.le_div_iff_mul_le (Fact.out : p.Prime).pos).mpr (by simpa using hp_hi)
    have hhi : Y < 2 * p := by omega
    have hlt : Y / p < 2 := Nat.div_lt_of_lt_mul (by linarith)
    omega
  have h2 : 2 * Y / p = 2 := by
    have hlo : 2 ≤ 2 * Y / p :=
      (Nat.le_div_iff_mul_le (Fact.out : p.Prime).pos).mpr (by linarith)
    have hhi : 2 * Y < 3 * p := by omega
    have hlt : 2 * Y / p < 3 := Nat.div_lt_of_lt_mul (by linarith)
    omega
  rw [h1, h2]

private lemma card_primes_Ioc_ge :
    ∀ᶠ Y : ℕ in atTop,
      (Y : ℝ) / (4 * Real.log (2 * Y)) ≤ (((Finset.Ioc Y (2 * Y)).filter Nat.Prime).card : ℝ) := by
  have hlog_bound : ∀ u : ℝ, 0 < u → Real.log u ≤ 4 * u ^ (1 / 4 : ℝ) := by
    intro u hu
    have hpow_pos : 0 < u ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hu _
    have h1 := Real.log_le_sub_one_of_pos hpow_pos
    rw [Real.log_rpow hu] at h1
    linarith
  have hlog4_gt : 1 < Real.log 4 := by
    have he := Real.exp_one_lt_d9
    have h4 : Real.exp 1 < (4 : ℝ) := by linarith
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) h4
  filter_upwards [eventually_ge_atTop (400 ^ 4)] with Y hY_big
  have hY5 : 5 ≤ Y := by omega
  have hY1 : 1 ≤ Y := by omega
  have hY_pos : (0 : ℝ) < Y := by positivity
  have hY1_r : (1 : ℝ) ≤ Y := by exact_mod_cast hY1
  have hsqrt_le_two_thirds : Nat.sqrt (2 * Y) ≤ 2 * Y / 3 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 3)]
    have hsq : Nat.sqrt (2 * Y) ^ 2 ≤ 2 * Y := by
      rw [pow_two]
      exact Nat.sqrt_le (2 * Y)
    nlinarith
  have hsqrt_le_Y : Nat.sqrt (2 * Y) ≤ Y := by
    have : 2 * Y / 3 ≤ Y := by omega
    omega
  let S_all := (Finset.Icc 2 (2 * Y)).filter Nat.Prime
  let P1 := S_all.filter (fun p => p ≤ Nat.sqrt (2 * Y))
  let P2 := S_all.filter (fun p => Nat.sqrt (2 * Y) < p ∧ p ≤ 2 * Y / 3)
  let P3 := S_all.filter (fun p => 2 * Y / 3 < p ∧ p ≤ Y)
  let P4 := (Finset.Ioc Y (2 * Y)).filter Nat.Prime
  have hS_split : S_all = P1 ∪ P2 ∪ P3 ∪ P4 := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc,
      S_all, P1, P2, P3, P4]
    constructor
    · rintro ⟨⟨hp2, hp2Y⟩, hp⟩
      by_cases h1 : p ≤ Nat.sqrt (2 * Y)
      · exact Or.inl (Or.inl (Or.inl ⟨⟨⟨hp2, hp2Y⟩, hp⟩, h1⟩))
      · by_cases h2 : p ≤ 2 * Y / 3
        · exact Or.inl (Or.inl (Or.inr ⟨⟨⟨hp2, hp2Y⟩, hp⟩, by omega, h2⟩))
        · by_cases h3 : p ≤ Y
          · exact Or.inl (Or.inr ⟨⟨⟨hp2, hp2Y⟩, hp⟩, by omega, h3⟩)
          · exact Or.inr ⟨⟨by omega, hp2Y⟩, hp⟩
    · rintro (((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) | ⟨⟨hpY, hp2Y⟩, hp⟩)
      · exact h
      · exact h
      · exact h
      · exact ⟨⟨hp.two_le, hp2Y⟩, hp⟩
  have hdisj12 : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]; intro p h1 h2
    simp only [Finset.mem_filter, P1, P2] at h1 h2; omega
  have hdisj123 : Disjoint (P1 ∪ P2) P3 := by
    rw [Finset.disjoint_left]; intro p h12 h3
    simp only [Finset.mem_union, Finset.mem_filter, P1, P2, P3] at h12 h3
    rcases h12 with h1 | h2 <;> omega
  have hdisj1234 : Disjoint (P1 ∪ P2 ∪ P3) P4 := by
    rw [Finset.disjoint_left]; intro p h123 h4
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc,
      S_all, P1, P2, P3, P4] at h123 h4
    rcases h123 with ((h1 | h2) | h3) <;> omega
  have hcb_fac : Y.centralBinom =
      ∏ p ∈ S_all, p ^ padicValNat p Y.centralBinom := by
    have hprod := Nat.prod_factorization_pow_eq_self Y.centralBinom_pos.ne'
    have hsub : Y.centralBinom.primeFactors ⊆ S_all := by
      intro p hp
      have hp_prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd_cb : p ∣ Y.centralBinom := Nat.dvd_of_mem_primeFactors hp
      have hp_dvd_fac : p ∣ Nat.factorial (2 * Y) := by
        refine hp_dvd_cb.trans ⟨Nat.factorial Y * Nat.factorial Y, ?_⟩
        exact (centralBinom_mul_sq_factorial Y).symm
      have hp_le : p ≤ 2 * Y := (hp_prime.dvd_factorial).mp hp_dvd_fac
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.two_le, hp_le⟩, hp_prime⟩
    have hprod2 : ∏ p ∈ Y.centralBinom.primeFactors, p ^ Y.centralBinom.factorization p =
        ∏ p ∈ S_all, p ^ Y.centralBinom.factorization p := by
      refine Finset.prod_subset hsub fun p _ hp_not => ?_
      have hnot_supp : p ∉ Y.centralBinom.factorization.support := by
        simpa [Nat.support_factorization] using hp_not
      rw [Finsupp.notMem_support_iff.mp hnot_supp, pow_zero]
    have hprod_eq : (Y.centralBinom.factorization.prod fun x1 x2 => x1 ^ x2) =
        ∏ p ∈ Y.centralBinom.primeFactors, p ^ Y.centralBinom.factorization p := by
      rfl
    rw [hprod_eq, hprod2] at hprod
    conv_lhs => rw [← hprod]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp_prime := (Finset.mem_filter.mp hp).2
    rw [Nat.factorization_def _ hp_prime]
  have hprod_split : Y.centralBinom =
      (∏ p ∈ P1, p ^ padicValNat p Y.centralBinom) *
      (∏ p ∈ P2, p ^ padicValNat p Y.centralBinom) *
      (∏ p ∈ P3, p ^ padicValNat p Y.centralBinom) *
      (∏ p ∈ P4, p ^ padicValNat p Y.centralBinom) := by
    conv_lhs => rw [hcb_fac, hS_split]
    rw [Finset.prod_union hdisj1234, Finset.prod_union hdisj123, Finset.prod_union hdisj12]
  have hP1_le : ∏ p ∈ P1, p ^ padicValNat p Y.centralBinom ≤ (2 * Y) ^ Nat.sqrt (2 * Y) := by
    have hfac : ∀ p ∈ P1, p ^ padicValNat p Y.centralBinom ≤ 2 * Y := by
      intro p hp
      have hp_prim : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      let : Fact p.Prime := ⟨hp_prim⟩
      exact (Nat.pow_le_pow_right hp_prim.pos (padicValNat_centralBinom_le_log hY1)).trans
        (Nat.pow_log_le_self p (by omega))
    have hcard : P1.card ≤ Nat.sqrt (2 * Y) := by
      have h1 : P1 ⊆ Finset.Icc 1 (Nat.sqrt (2 * Y)) := by
        intro p hp
        simp only [Finset.mem_filter, Finset.mem_Icc, S_all, P1] at hp
        exact Finset.mem_Icc.mpr ⟨by omega, hp.2⟩
      exact (Finset.card_le_card h1).trans (by simp)
    calc ∏ p ∈ P1, p ^ padicValNat p Y.centralBinom
        ≤ ∏ _p ∈ P1, (2 * Y) := Finset.prod_le_prod' hfac
      _ = (2 * Y) ^ P1.card := Finset.prod_const _
      _ ≤ (2 * Y) ^ Nat.sqrt (2 * Y) := Nat.pow_le_pow_right (by omega) hcard
  have hP2_le : ∏ p ∈ P2, p ^ padicValNat p Y.centralBinom ≤ 4 ^ (2 * Y / 3) := by
    have hfac : ∀ p ∈ P2, p ^ padicValNat p Y.centralBinom ≤ p := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, S_all, P2] at hp
      have hp_prim : p.Prime := hp.1.2
      let : Fact p.Prime := ⟨hp_prim⟩
      have hv := padicValNat_centralBinom_le_one_of_sqrt_lt hY1 hp.2.1
      calc p ^ padicValNat p Y.centralBinom ≤ p ^ 1 := Nat.pow_le_pow_right hp_prim.pos hv
        _ = p := pow_one p
    have hsub : P2 ⊆ (Finset.range (2 * Y / 3 + 1)).filter Nat.Prime := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, S_all, P2] at hp ⊢
      exact ⟨by omega, hp.1.2⟩
    calc ∏ p ∈ P2, p ^ padicValNat p Y.centralBinom
        ≤ ∏ p ∈ P2, p := Finset.prod_le_prod' hfac
      _ ≤ ∏ p ∈ (Finset.range (2 * Y / 3 + 1)).filter Nat.Prime, p :=
          Finset.prod_le_prod_of_subset_of_one_le' hsub fun p hp _ =>
            (Finset.mem_filter.mp hp).2.one_le
      _ = primorial (2 * Y / 3) := by unfold primorial; rfl
      _ ≤ 4 ^ (2 * Y / 3) := primorial_le_four_pow (2 * Y / 3)
  have hP3_eq : ∏ p ∈ P3, p ^ padicValNat p Y.centralBinom = 1 := by
    refine Finset.prod_eq_one fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_Icc, S_all, P3] at hp
    let : Fact p.Prime := ⟨hp.1.2⟩
    rw [padicValNat_centralBinom_eq_zero_of_mid hY5 hp.2.1 hp.2.2, pow_zero]
  have hP4_le : ∏ p ∈ P4, p ^ padicValNat p Y.centralBinom ≤ (2 * Y) ^ P4.card := by
    have hfac : ∀ p ∈ P4, p ^ padicValNat p Y.centralBinom ≤ 2 * Y := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_Ioc, P4] at hp
      let : Fact p.Prime := ⟨hp.2⟩
      have hsqrt_lt : Nat.sqrt (2 * Y) < p := by omega
      have hv := padicValNat_centralBinom_le_one_of_sqrt_lt hY1 hsqrt_lt
      have h1 : p ^ padicValNat p Y.centralBinom ≤ p ^ 1 := Nat.pow_le_pow_right hp.2.pos hv
      exact h1.trans (by simpa using hp.1.2)
    calc ∏ p ∈ P4, p ^ padicValNat p Y.centralBinom
        ≤ ∏ _p ∈ P4, (2 * Y) := Finset.prod_le_prod' hfac
      _ = (2 * Y) ^ P4.card := Finset.prod_const _
  have hnat_ineq : 4 ^ Y ≤ (2 * Y + 1) * (2 * Y) ^ Nat.sqrt (2 * Y) * 4 ^ (2 * Y / 3) * (2 * Y) ^ P4.card := by
    have h1 := four_pow_le_succ_mul_centralBinom Y
    rw [hprod_split, hP3_eq, mul_one] at h1
    calc 4 ^ Y ≤ (2 * Y + 1) * ((∏ p ∈ P1, _) * (∏ p ∈ P2, _) * (∏ p ∈ P4, _)) := h1
      _ ≤ (2 * Y + 1) * ((2 * Y) ^ Nat.sqrt (2 * Y) * 4 ^ (2 * Y / 3) * (2 * Y) ^ P4.card) := by
          gcongr
      _ = _ := by ring
  have hreal_ineq : ((4 : ℝ) ^ Y) ≤
      (2 * Y + 1 : ℝ) * (2 * Y : ℝ) ^ Nat.sqrt (2 * Y) * (4 : ℝ) ^ (2 * Y / 3) * (2 * Y : ℝ) ^ P4.card := by
    exact_mod_cast hnat_ineq
  have hlog_ineq : (Y : ℝ) * Real.log 4 ≤
      Real.log (2 * Y + 1) + (Nat.sqrt (2 * Y) : ℝ) * Real.log (2 * Y) +
        ((2 * Y / 3 : ℕ) : ℝ) * Real.log 4 + (P4.card : ℝ) * Real.log (2 * Y) := by
    have hpos_lhs : (0 : ℝ) < (4 : ℝ) ^ Y := by positivity
    have hpos_rhs : (0 : ℝ) < (2 * Y + 1 : ℝ) * (2 * Y : ℝ) ^ Nat.sqrt (2 * Y) *
        (4 : ℝ) ^ (2 * Y / 3) * (2 * Y : ℝ) ^ P4.card := by positivity
    have h := Real.log_le_log hpos_lhs hreal_ineq
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at h
    exact h
  have h2Y3_le : ((2 * Y / 3 : ℕ) : ℝ) ≤ 2 * (Y : ℝ) / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    exact_mod_cast Nat.div_mul_le_self (2 * Y) 3
  have hsqrt_le : (Nat.sqrt (2 * Y) : ℝ) + 1 ≤ 2 * (2 * (Y : ℝ)) ^ (1 / 2 : ℝ) := by
    have h1 : (Nat.sqrt (2 * Y) : ℝ) ≤ Real.sqrt (2 * Y) := by
      rw [Real.le_sqrt (Nat.cast_nonneg _) (by positivity)]
      exact_mod_cast (by rw [pow_two]; exact Nat.sqrt_le (2 * Y) : Nat.sqrt (2 * Y) ^ 2 ≤ 2 * Y)
    have h2 : Real.sqrt (2 * Y) = (2 * (Y : ℝ)) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have h3 : (1 : ℝ) ≤ (2 * (Y : ℝ)) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    linarith
  have hlog2Y_le : Real.log (2 * Y) ≤ Real.log (2 * Y + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsmall_term : Real.log (2 * Y + 1) + (Nat.sqrt (2 * Y) : ℝ) * Real.log (2 * Y) ≤
      ((1 : ℝ) / 12) * Y := by
    have hlog_rpow := hlog_bound (2 * Y + 1 : ℝ) (by positivity)
    have h2Y1_le : (2 * (Y : ℝ) + 1) ^ (1 / 4 : ℝ) ≤ (3 * (Y : ℝ)) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hprod_rpow : ((Nat.sqrt (2 * Y) : ℝ) + 1) * Real.log (2 * Y + 1) ≤
        2 * (2 * (Y : ℝ)) ^ (1 / 2 : ℝ) * (4 * (3 * (Y : ℝ)) ^ (1 / 4 : ℝ)) := by
      have hlog_le3 : Real.log (2 * (Y : ℝ) + 1) ≤ 4 * (3 * (Y : ℝ)) ^ (1 / 4 : ℝ) := by linarith
      have hsq_nn : 0 ≤ (Nat.sqrt (2 * Y) : ℝ) + 1 := by positivity
      exact mul_le_mul hsqrt_le hlog_le3 (Real.log_nonneg (by linarith)) (by positivity)
    have hY4_le : (400 : ℝ) ≤ (Y : ℝ) ^ (1 / 4 : ℝ) := by
      have h400 : (400 : ℝ) ^ (4 : ℝ) ≤ (Y : ℝ) := by
        exact_mod_cast hY_big
      calc (400 : ℝ) = ((400 : ℝ) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ (Y : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h400 (by norm_num)
    have hpow_comb : (2 * (Y : ℝ)) ^ (1 / 2 : ℝ) * (3 * (Y : ℝ)) ^ (1 / 4 : ℝ) ≤
        4 * (Y : ℝ) ^ (3 / 4 : ℝ) := by
      rw [Real.mul_rpow (by norm_num) hY_pos.le, Real.mul_rpow (by norm_num) hY_pos.le]
      have h2_le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      have h3_le : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
        have h3_lt : ((3 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 < 2 ^ 4 := by
          rw [← Real.rpow_natCast ((3 : ℝ) ^ (1 / 4 : ℝ)) 4, ← Real.rpow_mul (by norm_num)]
          norm_num
        by_contra hlt
        push Not at hlt
        have := pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 4 ≠ 0)
        linarith
      have hY_add : (Y : ℝ) ^ (1 / 2 : ℝ) * (Y : ℝ) ^ (1 / 4 : ℝ) = (Y : ℝ) ^ (3 / 4 : ℝ) := by
        rw [← Real.rpow_add hY_pos]; norm_num
      calc (2 : ℝ) ^ (1 / 2 : ℝ) * (Y : ℝ) ^ (1 / 2 : ℝ) * ((3 : ℝ) ^ (1 / 4 : ℝ) * (Y : ℝ) ^ (1 / 4 : ℝ))
          = ((2 : ℝ) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ (1 / 4 : ℝ)) * ((Y : ℝ) ^ (1 / 2 : ℝ) * (Y : ℝ) ^ (1 / 4 : ℝ)) := by ring
        _ ≤ (2 * 2) * (Y : ℝ) ^ (3 / 4 : ℝ) := by
            rw [hY_add]
            exact mul_le_mul_of_nonneg_right (mul_le_mul h2_le h3_le (by positivity) (by norm_num)) (by positivity)
        _ = 4 * (Y : ℝ) ^ (3 / 4 : ℝ) := by ring
    have hY34_le : 32 * (Y : ℝ) ^ (3 / 4 : ℝ) ≤ (1 / 12 : ℝ) * Y := by
      have hmul34 : (Y : ℝ) ^ (3 / 4 : ℝ) * (Y : ℝ) ^ (1 / 4 : ℝ) = (Y : ℝ) := by
        rw [← Real.rpow_add hY_pos]; norm_num
      nlinarith [hY4_le, hmul34, Real.rpow_nonneg hY_pos.le (3 / 4 : ℝ)]
    have hstep1 : Real.log (2 * Y + 1) + (Nat.sqrt (2 * Y) : ℝ) * Real.log (2 * Y) ≤
        ((Nat.sqrt (2 * Y) : ℝ) + 1) * Real.log (2 * Y + 1) := by
      have hsq_nn : 0 ≤ (Nat.sqrt (2 * Y) : ℝ) := Nat.cast_nonneg _
      nlinarith [hlog2Y_le]
    nlinarith [hstep1, hprod_rpow, hpow_comb, hY34_le]
  have hlog2Y_pos : 0 < Real.log (2 * Y) := Real.log_pos (by linarith)
  have hfinal_mul : (Y : ℝ) ≤ 4 * Real.log (2 * Y) * (P4.card : ℝ) := by
    have hlog4_nn : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have h1 : (Y : ℝ) * (1 / 3 * Real.log 4 - 1 / 12) ≤ (P4.card : ℝ) * Real.log (2 * Y) := by
      have hmul : ((2 * Y / 3 : ℕ) : ℝ) * Real.log 4 ≤ (2 * (Y : ℝ) / 3) * Real.log 4 :=
        mul_le_mul_of_nonneg_right h2Y3_le hlog4_nn
      linarith [hlog_ineq, hsmall_term, hmul]
    have hcoeff : (1 / 4 : ℝ) ≤ 1 / 3 * Real.log 4 - 1 / 12 := by linarith [hlog4_gt]
    nlinarith [h1, hcoeff, hY_pos]
  rw [div_le_iff₀ (by positivity)]
  linarith

private noncomputable def e (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * x)

private lemma e_zero : e 0 = 1 := by
  simp [e]

private lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  simp only [e, Complex.ofReal_add, mul_add, Complex.exp_add]

private lemma e_neg (x : ℝ) : e (-x) = star (e x) := by
  dsimp [e]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

private lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  dsimp [e]
  rw [show (2 : ℂ) * Real.pi * Complex.I * x = (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma e_add_one (x : ℝ) : e (x + 1) = e x := by
  rw [e_add]
  have h1 : e 1 = 1 := by
    dsimp [e]
    simp [Complex.exp_two_pi_mul_I]
  rw [h1, mul_one]

private lemma e_sub_one (x : ℝ) : e (x - 1) = e x := by
  have h := e_add_one (x - 1)
  rw [sub_add_cancel] at h
  exact h.symm

private lemma e_add_nat (x : ℝ) (n : ℕ) : e (x + n) = e x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, e_add_one, ih]

private lemma e_sub_nat (x : ℝ) (n : ℕ) : e (x - n) = e x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, ← sub_sub, e_sub_one, ih]

private lemma e_add_int (x : ℝ) (k : ℤ) : e (x + k) = e x := by
  cases k with
  | ofNat n => simpa using e_add_nat x n
  | negSucc n =>
    rw [Int.cast_negSucc, ← sub_eq_add_neg]
    exact e_sub_nat x (n + 1)

private noncomputable def fejerKernel (H : ℕ) (u : ℝ) : ℝ :=
  (1 / ((H : ℝ) + 1)) * ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ ^ 2

private lemma fejerKernel_nonneg (H : ℕ) (u : ℝ) : 0 ≤ fejerKernel H u := by
  dsimp [fejerKernel]; positivity

private lemma fejerKernel_periodic (H : ℕ) (u : ℝ) : fejerKernel H (u + 1) = fejerKernel H u := by
  refine congr_arg (fun z : ℂ => (1 / ((H : ℝ) + 1)) * ‖z‖ ^ 2) ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, mul_one, e_add_nat]

private lemma fejerKernel_add_int (H : ℕ) (u : ℝ) (m : ℤ) :
    fejerKernel H (u + m) = fejerKernel H u := by
  refine congr_arg (fun z : ℂ => (1 / ((H : ℝ) + 1)) * ‖z‖ ^ 2) ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_add, show (k : ℝ) * (m : ℤ) = ((k : ℤ) * m : ℤ) by push_cast; ring, e_add_int]

private lemma fejerKernel_eq_sum (H : ℕ) (u : ℝ) :
    (fejerKernel H u : ℂ) =
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        (((1 - (|h| : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) * e ((h : ℝ) * u) := by
  let S : ℂ := ∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)
  have hnormSq : ((‖S‖ ^ 2 : ℝ) : ℂ) = S * star S := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rfl
  have hstar : star S = ∑ l ∈ Finset.range (H + 1), e (-(l : ℝ) * u) := by
    change (starRingEnd ℂ) (∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    change star (e ((l : ℝ) * u)) = _
    rw [← e_neg]
    congr 1; ring
  have hprod : S * star S =
      ∑ p ∈ Finset.range (H + 1) ×ˢ Finset.range (H + 1),
        e (((p.1 : ℤ) - (p.2 : ℤ) : ℝ) * u) := by
    rw [hstar, Finset.sum_mul_sum]
    symm
    rw [Finset.sum_product]
    symm
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [← e_add]
    congr 1
    push_cast
    ring
  have hfiber :
      ∑ p ∈ Finset.range (H + 1) ×ˢ Finset.range (H + 1),
        e (((p.1 : ℤ) - (p.2 : ℤ) : ℝ) * u) =
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        (((H + 1 - h.natAbs : ℕ) : ℝ) : ℂ) * e ((h : ℝ) * u) := by
    have hmap : ∀ p ∈ Finset.range (H + 1) ×ˢ Finset.range (H + 1),
        (p.1 : ℤ) - (p.2 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := by
      intro p hp
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
      rw [Finset.mem_Icc]
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => e (((p.1 : ℤ) - (p.2 : ℤ) : ℝ) * u))]
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [Finset.mem_Icc] at hh
    let fiber := (Finset.range (H + 1) ×ˢ Finset.range (H + 1)).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = h)
    have hsum_const : ∑ p ∈ fiber, e (((p.1 : ℤ) - (p.2 : ℤ) : ℝ) * u) =
        (fiber.card : ℂ) * e ((h : ℝ) * u) := by
      trans ∑ _p ∈ fiber, e ((h : ℝ) * u)
      · refine Finset.sum_congr rfl fun p hp => ?_
        have hdiff : (p.1 : ℤ) - (p.2 : ℤ) = h := (Finset.mem_filter.mp hp).2
        have hdiff_r : ((p.1 : ℤ) - (p.2 : ℤ) : ℝ) = (h : ℝ) := by exact_mod_cast hdiff
        rw [hdiff_r]
      · simp
    have hcard_fiber : fiber.card = H + 1 - h.natAbs := by
      have hbij : fiber.card = (Finset.range (H + 1 - h.natAbs)).card := by
        refine Finset.card_bij (fun p _ => min p.1 p.2) ?_ ?_ ?_
        · intro p hp
          rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
          rw [Finset.mem_range]
          omega
        · intro a ha b hb hab
          rw [Finset.mem_filter] at ha hb
          ext <;> omega
        · intro m hm
          rw [Finset.mem_range] at hm
          by_cases h0 : 0 ≤ h
          · refine ⟨(m + h.natAbs, m), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega⟩, by omega⟩
          · refine ⟨(m, m + h.natAbs), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
              ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega⟩, by omega⟩
      simpa using hbij
    rw [hsum_const, hcard_fiber]
    push_cast
    rfl
  dsimp [fejerKernel]
  push_cast
  rw [show ((‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ : ℝ) : ℂ) ^ 2 = ((‖S‖ ^ 2 : ℝ) : ℂ) by
    rw [Complex.ofReal_pow],
    hnormSq, hprod, hfiber, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mem_Icc] at hh
  have hle : h.natAbs ≤ H + 1 := by omega
  have hH_pos : ((H : ℝ) + 1) ≠ 0 := by positivity
  have habs_cast : (|(h : ℝ)| : ℝ) = (h.natAbs : ℝ) := by
    cases h with
    | ofNat n => simp
    | negSucc n =>
      rw [Int.cast_negSucc, Int.natAbs_negSucc, Nat.cast_add, Nat.cast_one,
        abs_of_neg (by linarith [Nat.cast_nonneg (α := ℝ) n]), neg_neg]
  rw [Nat.cast_sub hle, habs_cast]
  push_cast
  field_simp [hH_pos]

private lemma norm_e_sub_one (u : ℝ) :
    ‖e u - 1‖ = 2 * |Real.sin (Real.pi * u)| := by
  have hdecomp : e u - 1 = Complex.exp (Real.pi * Complex.I * u) *
      (Complex.exp (Real.pi * Complex.I * u) - Complex.exp (-(Real.pi * Complex.I * u))) := by
    dsimp [e]
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    have h1 : Real.pi * Complex.I * u + Real.pi * Complex.I * u = 2 * Real.pi * Complex.I * u := by ring
    have h2 : Real.pi * Complex.I * u + -(Real.pi * Complex.I * u) = 0 := by ring
    rw [h1, h2, Complex.exp_zero]
  have hsin : Complex.exp (Real.pi * Complex.I * u) - Complex.exp (-(Real.pi * Complex.I * u)) =
      2 * (Real.sin (Real.pi * u) : ℂ) * Complex.I := by
    rw [show Real.pi * Complex.I * u = ((Real.pi * u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      show -(↑(Real.pi * u) * Complex.I) = ((-((Real.pi * u : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hdecomp, hsin, norm_mul]
  have hn1 : ‖Complex.exp (Real.pi * Complex.I * u)‖ = 1 := by
    rw [show Real.pi * Complex.I * u = ((Real.pi * u : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [hn1, one_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs]

private lemma fejerKernel_le_of_mem_Icc {H : ℕ} {δ u : ℝ} (hδ0 : 0 < δ) (_hδ : δ ≤ 1 / 4)
    (hu : u ∈ Set.Icc δ (1 - δ)) :
    fejerKernel H u ≤ 1 / (4 * ((H : ℝ) + 1) * δ ^ 2) := by
  have hsin_ge : 2 * δ ≤ |Real.sin (Real.pi * u)| := by
    by_cases hu_half : u ≤ 1 / 2
    · have h0 : 0 ≤ Real.pi * u := mul_nonneg Real.pi_pos.le (by linarith [hu.1])
      have hpi2 : Real.pi * u ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
      have hmul := Real.mul_le_sin h0 hpi2
      have hge : 2 * δ ≤ Real.sin (Real.pi * u) := by
        calc 2 * δ ≤ 2 * u := by linarith [hu.1]
          _ = 2 / Real.pi * (Real.pi * u) := by field_simp [Real.pi_ne_zero]
          _ ≤ Real.sin (Real.pi * u) := hmul
      exact hge.trans (le_abs_self _)
    · have hu_gt : 1 / 2 < u := lt_of_not_ge hu_half
      have h0 : 0 ≤ Real.pi * (1 - u) := mul_nonneg Real.pi_pos.le (by linarith [hu.2])
      have hpi2 : Real.pi * (1 - u) ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
      have hmul := Real.mul_le_sin h0 hpi2
      have hsin_eq : Real.sin (Real.pi * u) = Real.sin (Real.pi * (1 - u)) := by
        rw [show Real.pi * (1 - u) = Real.pi - Real.pi * u by ring, Real.sin_pi_sub]
      have hge : 2 * δ ≤ Real.sin (Real.pi * u) := by
        rw [hsin_eq]
        calc 2 * δ ≤ 2 * (1 - u) := by linarith [hu.2]
          _ = 2 / Real.pi * (Real.pi * (1 - u)) := by field_simp [Real.pi_ne_zero]
          _ ≤ Real.sin (Real.pi * (1 - u)) := hmul
      exact hge.trans (le_abs_self _)
  have hnorm_ge : 4 * δ ≤ ‖e u - 1‖ := by
    rw [norm_e_sub_one]
    linarith
  have he_ne : e u ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hnorm_ge
    linarith
  have hgeom : (∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)) * (e u - 1) =
      e (((H + 1 : ℕ) : ℝ) * u) - 1 := by
    have hpow : ∀ k : ℕ, e ((k : ℝ) * u) = (e u) ^ k := by
      intro k
      induction k with
      | zero => simp [e_zero]
      | succ k ih =>
        push_cast
        rw [add_mul, one_mul, e_add, ih, pow_succ]
    simp_rw [hpow]
    rw [geom_sum_mul]
  have hnorm_sum : ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ ≤ 1 / (2 * δ) := by
    have h1 : ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ * ‖e u - 1‖ ≤ 2 := by
      rw [← norm_mul, hgeom]
      calc ‖e (((H + 1 : ℕ) : ℝ) * u) - 1‖
          ≤ ‖e (((H + 1 : ℕ) : ℝ) * u)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [norm_e, norm_one]
        _ = 2 := by norm_num
    have h2 : ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ * (4 * δ) ≤ 2 := by
      calc ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ * (4 * δ)
          ≤ ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ * ‖e u - 1‖ :=
            mul_le_mul_of_nonneg_left hnorm_ge (norm_nonneg _)
        _ ≤ 2 := h1
    rw [le_div_iff₀ (by positivity)]
    linarith
  dsimp [fejerKernel]
  have hsq : ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ ^ 2 ≤ (1 / (2 * δ)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm_sum 2
  calc 1 / ((H : ℝ) + 1) * ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * u)‖ ^ 2
      ≤ 1 / ((H : ℝ) + 1) * (1 / (2 * δ)) ^ 2 := by gcongr
    _ = 1 / (4 * ((H : ℝ) + 1) * δ ^ 2) := by field_simp; ring

private lemma integral_e_mul_eq_zero {h : ℤ} (hh : h ≠ 0) (y : ℝ) :
    ∫ t in (0 : ℝ)..1, e ((h : ℝ) * (y - t)) = 0 := by
  have hc_ne : (-((2 : ℂ) * Real.pi * Complex.I * (h : ℤ))) ≠ 0 := by
    refine neg_ne_zero.mpr ?_
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero) ?_
    · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact Int.cast_ne_zero.mpr hh
  have hfn : ∀ t : ℝ, e ((h : ℝ) * (y - t)) =
      e ((h : ℝ) * y) * Complex.exp ((-((2 : ℂ) * Real.pi * Complex.I * (h : ℤ))) * t) := by
    intro t
    rw [mul_sub, sub_eq_add_neg, e_add]
    congr 1
    dsimp [e]
    congr 1
    push_cast
    ring
  simp_rw [hfn, intervalIntegral.integral_const_mul]
  rw [integral_exp_mul_complex hc_ne]
  have hexp1 : Complex.exp ((-((2 : ℂ) * Real.pi * Complex.I * (h : ℤ))) * (1 : ℝ)) = 1 := by
    rw [show ((-((2 : ℂ) * Real.pi * Complex.I * (h : ℤ))) * (1 : ℝ)) =
      ((( (-h : ℤ) : ℂ) * (2 * Real.pi * Complex.I))) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-h)
  have hexp0 : Complex.exp ((-((2 : ℂ) * Real.pi * Complex.I * (h : ℤ))) * (0 : ℝ)) = 1 := by
    simp
  rw [hexp1, hexp0, sub_self, zero_div, mul_zero]

private lemma fejerKernel_integral_one (H : ℕ) (y : ℝ) :
    ∫ t in (0 : ℝ)..1, fejerKernel H (y - t) = 1 := by
  have hint_c : (((∫ t in (0 : ℝ)..1, fejerKernel H (y - t)) : ℝ) : ℂ) =
      ∫ t in (0 : ℝ)..1, (fejerKernel H (y - t) : ℂ) := by
    rw [intervalIntegral.integral_ofReal]
  have hsum_eq : ∫ t in (0 : ℝ)..1, (fejerKernel H (y - t) : ℂ) =
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        (((1 - (|h| : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, e ((h : ℝ) * (y - t)) := by
    simp_rw [fejerKernel_eq_sum]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro h _
      refine Continuous.intervalIntegrable ?_ _ _
      dsimp [e]
      fun_prop
  have h0_mem : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hsum_val : ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
      (((1 - (|h| : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1, e ((h : ℝ) * (y - t)) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [e_zero]
    · intro h _ hh0
      rw [integral_e_mul_eq_zero hh0 y, mul_zero]
    · intro hnot
      exact absurd h0_mem hnot
  have hre := congrArg Complex.re (hint_c.trans (hsum_eq.trans hsum_val))
  simpa using hre

private lemma fejerMajorant_exists (H : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 8)
    (hH : 1 / (4 * ((H : ℝ) + 1) * δ ^ 2) ≤ 1 / 2) :
    ∃ (c : ℤ → ℂ) (T : ℝ → ℝ),
      (∀ x : ℝ, ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * e ((h : ℝ) * x) = (T x : ℂ)) ∧
      (∀ x : ℝ, 0 ≤ T x) ∧
      (∀ x : ℝ, Int.fract x < 1 / 2 → 1 ≤ T x) ∧
      c 0 = (((1 / 2 + 2 * δ) / (1 - 1 / (4 * ((H : ℝ) + 1) * δ ^ 2)) : ℝ) : ℂ) ∧
      (∀ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖ ≤ 2) := by
  let η : ℝ := 1 / (4 * ((H : ℝ) + 1) * δ ^ 2)
  have hη_nn : 0 ≤ η := by dsimp [η]; positivity
  have h1η_pos : 0 < 1 - η := by dsimp [η] at *; linarith
  let P : ℝ → ℝ := fun x => ∫ t in (-δ)..(1 / 2 + δ), fejerKernel H (x - t)
  let c : ℤ → ℂ := fun h =>
    (((1 - (|h| : ℝ) / ((H : ℝ) + 1)) / (1 - η) : ℝ) : ℂ) *
      ∫ t in (-δ)..(1 / 2 + δ), e ((-(h : ℝ)) * t)
  let T : ℝ → ℝ := fun x => P x / (1 - η)
  refine ⟨c, T, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    have hP_c : ((P x : ℝ) : ℂ) = ∫ t in (-δ)..(1 / 2 + δ), (fejerKernel H (x - t) : ℂ) := by
      dsimp [P]
      rw [intervalIntegral.integral_ofReal]
    have hsum_P : (P x : ℂ) =
        ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
          (((1 - (|h| : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) *
            (∫ t in (-δ)..(1 / 2 + δ), e ((-(h : ℝ)) * t)) * e ((h : ℝ) * x) := by
      rw [hP_c]
      simp_rw [fejerKernel_eq_sum]
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun h _ => ?_
        have hmul_fn : ∀ t : ℝ,
            (((1 - (|h| : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) * e ((h : ℝ) * (x - t)) =
            ((((1 - (|h| : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) * e ((h : ℝ) * x)) * e ((-(h : ℝ)) * t) := by
          intro t
          rw [show (h : ℝ) * (x - t) = (h : ℝ) * x + (-(h : ℝ)) * t by ring, e_add]
          ring
        simp_rw [hmul_fn, intervalIntegral.integral_const_mul]
        ring
      · intro h _
        refine Continuous.intervalIntegrable ?_ _ _
        dsimp [e]
        fun_prop
    calc ∑ h ∈ Finset.Icc (-(H : ℤ)) H, c h * e ((h : ℝ) * x)
        = (1 / (1 - η) : ℂ) * ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
            (((1 - (|h| : ℝ) / ((H : ℝ) + 1)) : ℝ) : ℂ) *
              (∫ t in (-δ)..(1 / 2 + δ), e ((-(h : ℝ)) * t)) * e ((h : ℝ) * x) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          dsimp [c]
          push_cast
          ring
      _ = (1 / (1 - η) : ℂ) * (P x : ℂ) := by rw [← hsum_P]
      _ = (T x : ℂ) := by
          dsimp [T]
          push_cast
          ring
  · intro x
    refine div_nonneg ?_ h1η_pos.le
    refine intervalIntegral.integral_nonneg (by linarith) fun t _ => fejerKernel_nonneg H (x - t)
  · intro x hx
    let y := Int.fract x
    have hy0 : 0 ≤ y := Int.fract_nonneg x
    have hy12 : y < 1 / 2 := hx
    have hK_eq : ∀ t : ℝ, fejerKernel H (x - t) = fejerKernel H (y - t) := by
      intro t
      have hx_eq : x = y + (⌊x⌋ : ℤ) := by
        dsimp [y]
        rw [Int.fract, sub_add_cancel]
      rw [hx_eq, show (y + (⌊x⌋ : ℤ)) - t = (y - t) + (⌊x⌋ : ℤ) by ring, fejerKernel_add_int]
    have hP_eq : P x = ∫ t in (-δ)..(1 / 2 + δ), fejerKernel H (y - t) := by
      dsimp [P]
      simp_rw [hK_eq]
    have hcont : Continuous (fun t : ℝ => fejerKernel H (y - t)) := by
      have : ∀ t : ℝ, fejerKernel H (y - t) =
          (1 / ((H : ℝ) + 1)) * ‖∑ k ∈ Finset.range (H + 1), e ((k : ℝ) * (y - t))‖ ^ 2 := fun _ => rfl
      simp_rw [this]
      dsimp [e]
      fun_prop
    have hint_shift : ∫ t in (-δ)..(1 - δ), fejerKernel H (y - t) = 1 := by
      have hper : Function.Periodic (fun t : ℝ => fejerKernel H (y - t)) 1 := by
        intro t
        dsimp only
        rw [show y - (t + 1) = (y - t) + (-1 : ℤ) by push_cast; ring, fejerKernel_add_int]
      have h01 := hper.intervalIntegral_add_eq 0 (-δ)
      have heq01 : ∫ t in (0 : ℝ)..(0 + 1), fejerKernel H (y - t) = 1 := by
        simpa using fejerKernel_integral_one H y
      rw [show (-δ) + 1 = 1 - δ by ring] at h01
      linarith [h01, heq01]
    have hsplit : ∫ t in (-δ)..(1 - δ), fejerKernel H (y - t) =
        P x + ∫ t in (1 / 2 + δ)..(1 - δ), fejerKernel H (y - t) := by
      rw [hP_eq]
      exact (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable (-δ) (1 / 2 + δ))
        (hcont.intervalIntegrable (1 / 2 + δ) (1 - δ))).symm
    have htail_le : ∫ t in (1 / 2 + δ)..(1 - δ), fejerKernel H (y - t) ≤ η := by
      have hle_pt : ∀ t ∈ Set.Icc (1 / 2 + δ) (1 - δ), fejerKernel H (y - t) ≤ η := by
        intro t ht
        rw [← fejerKernel_periodic H (y - t)]
        refine fejerKernel_le_of_mem_Icc hδ0 (by linarith) ⟨?_, ?_⟩
        · linarith [ht.2, hy0]
        · linarith [ht.1, hy12]
      have hlen : (1 - δ) - (1 / 2 + δ) ≤ 1 := by linarith
      calc ∫ t in (1 / 2 + δ)..(1 - δ), fejerKernel H (y - t)
          ≤ ∫ _t in (1 / 2 + δ)..(1 - δ), η :=
            intervalIntegral.integral_mono_on (by linarith)
              (hcont.intervalIntegrable _ _) intervalIntegrable_const hle_pt
        _ = ((1 - δ) - (1 / 2 + δ)) * η := by simp
        _ ≤ 1 * η := mul_le_mul_of_nonneg_right hlen hη_nn
        _ = η := one_mul η
    have hP_ge : 1 - η ≤ P x := by linarith
    dsimp [T]
    exact (le_div_iff₀ h1η_pos).mpr (by linarith)
  · dsimp [c, η]
    simp only [abs_zero, Int.cast_zero, zero_div, sub_zero, neg_zero, zero_mul, e_zero,
      intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    ring
  · intro h hh
    rw [Finset.mem_Icc] at hh
    have hfac1 : |1 - (|h| : ℝ) / ((H : ℝ) + 1)| ≤ 1 := by
      have h1 : 0 ≤ (|h| : ℝ) / ((H : ℝ) + 1) := by positivity
      have h2 : (|h| : ℝ) / ((H : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have hab : |h| ≤ (H : ℤ) := abs_le.mpr hh
        have hab_r : (|h| : ℝ) ≤ H := by exact_mod_cast hab
        linarith
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hint_norm : ‖∫ t in (-δ)..(1 / 2 + δ), e ((-(h : ℝ)) * t)‖ ≤ 1 := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := -δ) (b := 1 / 2 + δ)
        (f := fun t => e ((-(h : ℝ)) * t)) (C := 1) (fun t _ => by rw [norm_e])
      have habs : |(1 / 2 + δ) - (-δ)| = 1 / 2 + 2 * δ := by
        rw [abs_of_nonneg (by linarith)]
        ring
      rw [habs] at h1
      linarith
    dsimp [c]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos h1η_pos]
    have hdiv_le : |1 - (|h| : ℝ) / ((H : ℝ) + 1)| / (1 - η) ≤ 2 := by
      rw [div_le_iff₀ h1η_pos]
      linarith
    calc |1 - (|h| : ℝ) / ((H : ℝ) + 1)| / (1 - η) *
          ‖∫ t in (-δ)..(1 / 2 + δ), e ((-(h : ℝ)) * t)‖
        ≤ 2 * 1 := mul_le_mul hdiv_le hint_norm (norm_nonneg _) (by norm_num)
      _ = 2 := mul_one 2

private def smallDigits (p s n : ℕ) : Prop :=
  ∀ j ∈ Finset.range s, 2 * basePDigit p n j < p

private instance (p s n : ℕ) : Decidable (smallDigits p s n) := by
  unfold smallDigits
  infer_instance

private lemma smallDigits_iff_highDigitCount_zero {p s n : ℕ} :
    smallDigits p s n ↔ highDigitCount p s n = 0 := by
  dsimp [smallDigits, highDigitCount]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h j hj
    exact not_le.mpr (h j hj)
  · intro h j hj
    exact lt_of_not_ge (h hj)

private lemma smallDigits_mod_pow {p s n : ℕ} (hp : 0 < p) :
    smallDigits p s (n % p ^ s) ↔ smallDigits p s n := by
  rw [smallDigits_iff_highDigitCount_zero, smallDigits_iff_highDigitCount_zero,
    highDigitCount_mod_pow hp]

private lemma smallDigits_step {p s q d : ℕ} (hp : 0 < p) (hd : d < p) :
    smallDigits p (s + 1) (q * p + d) ↔ smallDigits p s q ∧ 2 * d < p := by
  rw [smallDigits_iff_highDigitCount_zero, smallDigits_iff_highDigitCount_zero,
    highDigitCount_step hp hd]
  split_ifs with h0
  · simp [show ¬ 2 * d < p by omega]
  · simp [show 2 * d < p by omega]

private lemma card_smallDigits_period (p s : ℕ) (hp : 0 < p) :
    ((Finset.range (p ^ s)).filter (smallDigits p s)).card = ((p + 1) / 2) ^ s := by
  induction s with
  | zero =>
    have hfilt : (Finset.range (p ^ 0)).filter (smallDigits p 0) = {0} := by
      ext n
      simp only [pow_zero, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, smallDigits]
      constructor
      · intro hn; omega
      · rintro rfl; exact ⟨by omega, fun j hj => by simp at hj⟩
    rw [hfilt, Finset.card_singleton, pow_zero]
  | succ s ih =>
    let F := (Finset.range (p ^ (s + 1))).filter (smallDigits p (s + 1))
    let G := (Finset.range (p ^ s)).filter (smallDigits p s) ×ˢ Finset.range ((p + 1) / 2)
    have hbij : F.card = G.card := by
      refine Finset.card_bij (fun n _ => (n / p, n % p)) ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_range] at hn
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
        have hn_lt : n < p * p ^ s := by rw [pow_succ'] at hn; exact hn.1
        have hlt_q : n / p < p ^ s := Nat.div_lt_of_lt_mul hn_lt
        have hlt_d : n % p < p := Nat.mod_lt n hp
        have hn_eq : n = (n / p) * p + n % p := by
          rw [mul_comm, Nat.div_add_mod]
        have hsd := hn.2
        rw [hn_eq, smallDigits_step hp hlt_d] at hsd
        exact ⟨⟨hlt_q, hsd.1⟩, by omega⟩
      · intro a _ b _ hab
        have h1 : a / p = b / p := congrArg Prod.fst hab
        have h2 : a % p = b % p := congrArg Prod.snd hab
        have ha : a = p * (a / p) + a % p := (Nat.div_add_mod a p).symm
        have hb : b = p * (b / p) + b % p := (Nat.div_add_mod b p).symm
        rw [← h1, ← h2] at hb
        exact ha.trans hb.symm
      · rintro ⟨q, d⟩ hqd
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_range] at hqd
        have hd_lt : d < p := by omega
        have hqp_lt : q * p + d < p ^ (s + 1) := by
          rw [pow_succ]
          have h1 : q + 1 ≤ p ^ s := hqd.1.1
          have h2 : (q + 1) * p ≤ p ^ s * p := Nat.mul_le_mul_right p h1
          have h3 : q * p + d < (q + 1) * p := by rw [Nat.succ_mul]; omega
          exact lt_of_lt_of_le h3 h2
        refine ⟨q * p + d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqp_lt,
          (smallDigits_step hp hd_lt).mpr ⟨hqd.1.2, by omega⟩⟩, ?_⟩
        ext
        · dsimp; rw [mul_comm q p, Nat.mul_add_div hp, Nat.div_eq_of_lt hd_lt, add_zero]
        · dsimp; rw [mul_comm q p, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hd_lt]
    rw [hbij]
    dsimp [G]
    rw [Finset.card_product, ih, Finset.card_range, pow_succ]

private lemma card_smallDigits_range_bounds {p s X : ℕ} (hp : 0 < p) :
    (X / p ^ s) * ((p + 1) / 2) ^ s ≤ ((Finset.range X).filter (smallDigits p s)).card ∧
      ((Finset.range X).filter (smallDigits p s)).card ≤
        (X / p ^ s + 1) * ((p + 1) / 2) ^ s := by
  let P := p ^ s
  let Q := X / P
  have hP_pos : 0 < P := pow_pos hp s
  have hblocks : ∀ K : ℕ,
      ((Finset.range (K * P)).filter (smallDigits p s)).card = K * ((p + 1) / 2) ^ s := by
    intro K
    let F := (Finset.range (K * P)).filter (smallDigits p s)
    let G := Finset.range K ×ˢ ((Finset.range P).filter (smallDigits p s))
    have hbij : F.card = G.card := by
      refine Finset.card_bij (fun n _ => (n / P, n % P)) ?_ ?_ ?_
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_range] at hn
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_range]
        refine ⟨Nat.div_lt_of_lt_mul (by linarith), Nat.mod_lt n hP_pos, ?_⟩
        exact (smallDigits_mod_pow hp).mpr hn.2
      · intro a _ b _ hab
        have h1 : a / P = b / P := congrArg Prod.fst hab
        have h2 : a % P = b % P := congrArg Prod.snd hab
        have ha : a = P * (a / P) + a % P := (Nat.div_add_mod a P).symm
        have hb : b = P * (b / P) + b % P := (Nat.div_add_mod b P).symm
        rw [← h1, ← h2] at hb
        exact ha.trans hb.symm
      · rintro ⟨q, m⟩ hqm
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_range] at hqm
        have hlt : q * P + m < K * P := by
          have : q + 1 ≤ K := hqm.1
          nlinarith [hqm.2.1]
        have hmod_eq : (q * P + m) % P = m := by
          rw [mul_comm q P, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hqm.2.1]
        have hsd : smallDigits p s (q * P + m) := by
          rw [← smallDigits_mod_pow hp, hmod_eq]
          exact hqm.2.2
        refine ⟨q * P + m, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hsd⟩, ?_⟩
        ext
        · dsimp; rw [mul_comm q P, Nat.mul_add_div hP_pos, Nat.div_eq_of_lt hqm.2.1, add_zero]
        · exact hmod_eq
    rw [hbij]
    dsimp [G, P]
    rw [Finset.card_product, Finset.card_range, card_smallDigits_period p s hp]
  constructor
  · have hsub : (Finset.range (Q * P)).filter (smallDigits p s) ⊆
        (Finset.range X).filter (smallDigits p s) := by
      refine Finset.filter_subset_filter _ (Finset.range_mono ?_)
      dsimp [Q]
      exact Nat.div_mul_le_self X P
    calc Q * ((p + 1) / 2) ^ s
        = ((Finset.range (Q * P)).filter (smallDigits p s)).card := (hblocks Q).symm
      _ ≤ ((Finset.range X).filter (smallDigits p s)).card := Finset.card_le_card hsub
  · have hsub : (Finset.range X).filter (smallDigits p s) ⊆
        (Finset.range ((Q + 1) * P)).filter (smallDigits p s) := by
      refine Finset.filter_subset_filter _ (Finset.range_mono ?_)
      have hdm : P * Q + X % P = X := Nat.div_add_mod X P
      have hrm : X % P < P := Nat.mod_lt X hP_pos
      nlinarith
    calc ((Finset.range X).filter (smallDigits p s)).card
        ≤ ((Finset.range ((Q + 1) * P)).filter (smallDigits p s)).card := Finset.card_le_card hsub
      _ = (Q + 1) * ((p + 1) / 2) ^ s := hblocks (Q + 1)

private lemma norm_geom_sum_e_le_card (X : ℕ) (θ : ℝ) :
    ‖∑ n ∈ Finset.range X, e ((n : ℝ) * θ)‖ ≤ X := by
  calc ‖∑ n ∈ Finset.range X, e ((n : ℝ) * θ)‖
      ≤ ∑ n ∈ Finset.range X, ‖e ((n : ℝ) * θ)‖ := norm_sum_le _ _
    _ = ∑ _n ∈ Finset.range X, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun n _ => norm_e _
    _ = X := by simp

private lemma norm_geom_sum_e_le {X : ℕ} {θ : ℝ} (hθ0 : 0 < |θ|) (hθ : |θ| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range X, e ((n : ℝ) * θ)‖ ≤ 1 / (2 * |θ|) := by
  have hsin_ge : 2 * |θ| ≤ |Real.sin (Real.pi * θ)| := by
    have h0 : 0 ≤ Real.pi * |θ| := mul_nonneg Real.pi_pos.le (abs_nonneg θ)
    have hpi2 : Real.pi * |θ| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hmul := Real.mul_le_sin h0 hpi2
    have habs_sin : |Real.sin (Real.pi * θ)| = Real.sin (Real.pi * |θ|) := by
      rcases le_total 0 θ with hpos | hneg
      · have hsn : 0 ≤ Real.sin (Real.pi * θ) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le hpos)
            (by rw [abs_of_nonneg hpos] at hpi2; linarith [Real.pi_pos])
        rw [abs_of_nonneg hpos, abs_of_nonneg hsn]
      · have hpos' : 0 ≤ -θ := neg_nonneg.mpr hneg
        have hsn : 0 ≤ Real.sin (Real.pi * (-θ)) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le hpos')
            (by rw [abs_of_nonpos hneg] at hpi2; linarith [Real.pi_pos])
        have h_eq : Real.pi * θ = -(Real.pi * (-θ)) := by ring
        rw [h_eq, Real.sin_neg, abs_neg, abs_of_nonneg hsn, abs_of_nonpos hneg]
    rw [habs_sin]
    calc 2 * |θ| = 2 / Real.pi * (Real.pi * |θ|) := by field_simp [Real.pi_ne_zero]
      _ ≤ Real.sin (Real.pi * |θ|) := hmul
  have hnorm_ge : 4 * |θ| ≤ ‖e θ - 1‖ := by
    rw [norm_e_sub_one]
    linarith
  have hgeom : (∑ n ∈ Finset.range X, e ((n : ℝ) * θ)) * (e θ - 1) =
      e ((X : ℝ) * θ) - 1 := by
    have hpow : ∀ n : ℕ, e ((n : ℝ) * θ) = (e θ) ^ n := by
      intro n
      induction n with
      | zero => simp [e_zero]
      | succ n ih =>
        push_cast
        rw [add_mul, one_mul, e_add, ih, pow_succ]
    simp_rw [hpow]
    rw [geom_sum_mul]
  have h1 : ‖∑ n ∈ Finset.range X, e ((n : ℝ) * θ)‖ * ‖e θ - 1‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc ‖e ((X : ℝ) * θ) - 1‖
        ≤ ‖e ((X : ℝ) * θ)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + 1 := by rw [norm_e, norm_one]
      _ = 2 := by norm_num
  have h2 : ‖∑ n ∈ Finset.range X, e ((n : ℝ) * θ)‖ * (4 * |θ|) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hnorm_ge (norm_nonneg _)).trans h1
  rw [le_div_iff₀ (by positivity)]
  linarith

private noncomputable def freqSum {s : ℕ} (h : Fin s → ℤ) (p : ℕ) : ℝ :=
  ∑ j : Fin s, (h j : ℝ) / (p : ℝ) ^ (j.1 + 1)

private lemma abs_freqSum_le {s H Y p : ℕ} (hY : 1 ≤ Y) (hp : Y < p)
    (h : Fin s → ℤ) (hh : ∀ j, |h j| ≤ (H : ℤ)) :
    |freqSum h p| ≤ (s : ℝ) * H / Y := by
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hp_ge : (Y : ℝ) ≤ p := by exact_mod_cast hp.le
  have hp1 : (1 : ℝ) ≤ p := le_trans hY1 hp_ge
  have hp_pos : (0 : ℝ) < p := by linarith
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hterm : ∀ j : Fin s, |(h j : ℝ) / (p : ℝ) ^ (j.1 + 1)| ≤ (H : ℝ) / Y := by
    intro j
    have hj_abs : |(h j : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hh j
    have hpj_ge : (Y : ℝ) ≤ (p : ℝ) ^ (j.1 + 1) := by
      calc (Y : ℝ) ≤ (p : ℝ) := hp_ge
        _ = (p : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (p : ℝ) ^ (j.1 + 1) := pow_le_pow_right₀ hp1 (by omega)
    rw [abs_div, abs_of_pos (pow_pos hp_pos _)]
    calc |(h j : ℝ)| / (p : ℝ) ^ (j.1 + 1)
        ≤ (H : ℝ) / (p : ℝ) ^ (j.1 + 1) := div_le_div_of_nonneg_right hj_abs (by positivity)
      _ ≤ (H : ℝ) / Y := div_le_div_of_nonneg_left (by positivity) hY_pos hpj_ge
  calc |freqSum h p|
      ≤ ∑ j : Fin s, |(h j : ℝ) / (p : ℝ) ^ (j.1 + 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin s, (H : ℝ) / Y := Finset.sum_le_sum fun j _ => hterm j
    _ = (s : ℝ) * H / Y := by
        simp [Finset.sum_const]
        ring

private lemma sub_pow_factor_real (a b : ℝ) (m : ℕ) :
    b ^ m - a ^ m = (b - a) * ∑ i ∈ Finset.range m, b ^ i * a ^ (m - 1 - i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    · rw [Finset.sum_range_succ, mul_add]
      have hsub : ∀ i ∈ Finset.range m, (m + 1) - 1 - i = (m - 1 - i) + 1 := by
        intro i hi
        rw [Finset.mem_range] at hi
        omega
      have hsum_eq : ∑ i ∈ Finset.range m, b ^ i * a ^ (m + 1 - 1 - i) =
          a * ∑ i ∈ Finset.range m, b ^ i * a ^ (m - 1 - i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hsub i hi, pow_succ]
        ring
      rw [hsum_eq, show (b - a) * (a * ∑ i ∈ Finset.range m, b ^ i * a ^ (m - 1 - i)) =
          a * ((b - a) * ∑ i ∈ Finset.range m, b ^ i * a ^ (m - 1 - i)) by ring, ← ih]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one, pow_succ]
      ring

private lemma freq_sep {s H Y q₁ q₂ : ℕ} (hs : 1 ≤ s) (hY : 1 ≤ Y)
    (hq₁ : Y < q₁) (hq₁₂ : q₁ < q₂) (hq₂ : q₂ ≤ 2 * Y)
    (h' : Fin s → ℤ) (hne : h' ≠ 0) (hh : ∀ j, |h' j| ≤ (H : ℤ))
    (hdom : 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (s + 1) ≤ Y) :
    ((q₂ - q₁ : ℕ) : ℝ) / (2 * (2 * (Y : ℝ)) ^ (s + 1)) ≤ |freqSum h' q₁ - freqSum h' q₂| := by
  let S := Finset.univ.filter (fun j : Fin s => h' j ≠ 0)
  have hS_ne : S.Nonempty := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  let j₀ := S.min' hS_ne
  have hj₀_mem : j₀ ∈ S := Finset.min'_mem S hS_ne
  have hj₀_ne : h' j₀ ≠ 0 := (Finset.mem_filter.mp hj₀_mem).2
  have h_zero_lt : ∀ j : Fin s, j < j₀ → h' j = 0 := by
    intro j hj
    by_contra hnz
    have hj_mem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hnz⟩
    have := Finset.min'_le S j hj_mem
    exact absurd this (not_le.mpr hj)
  have hq1_r : (Y : ℝ) < q₁ := by exact_mod_cast hq₁
  have hq2_r : (q₁ : ℝ) < q₂ := by exact_mod_cast hq₁₂
  have hq2_ub : (q₂ : ℝ) ≤ 2 * Y := by exact_mod_cast hq₂
  have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hY_pos : (0 : ℝ) < Y := Nat.cast_pos.mpr (by omega)
  have hq1_pos : (0 : ℝ) < q₁ := lt_trans hY_pos hq1_r
  have hq2_pos : (0 : ℝ) < q₂ := lt_trans hq1_pos hq2_r
  have hdiff_pos : 0 < (q₂ : ℝ) - (q₁ : ℝ) := by linarith
  have hdiff_cast : ((q₂ - q₁ : ℕ) : ℝ) = (q₂ : ℝ) - (q₁ : ℝ) := by
    rw [Nat.cast_sub hq₁₂.le]
  let k := j₀.1 + 1
  have hk_ge1 : 1 ≤ k := Nat.succ_pos _
  have hk_le_s : k ≤ s := j₀.2
  let D_fn : ℕ → ℝ := fun m => 1 / (q₁ : ℝ) ^ m - 1 / (q₂ : ℝ) ^ m
  have hD_split : freqSum h' q₁ - freqSum h' q₂ =
      (h' j₀ : ℝ) * D_fn k + ∑ j ∈ Finset.univ.erase j₀, (h' j : ℝ) * D_fn (j.1 + 1) := by
    dsimp [freqSum, D_fn, k]
    rw [← Finset.sum_sub_distrib]
    have hcongr : ∀ j : Fin s, (h' j : ℝ) / (q₁ : ℝ) ^ (j.1 + 1) - (h' j : ℝ) / (q₂ : ℝ) ^ (j.1 + 1) =
        (h' j : ℝ) * (1 / (q₁ : ℝ) ^ (j.1 + 1) - 1 / (q₂ : ℝ) ^ (j.1 + 1)) := by
      intro j; ring
    simp_rw [hcongr]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j₀)]
  have hD_eq : ∀ m : ℕ, D_fn m =
      (((q₂ : ℝ) - (q₁ : ℝ)) * ∑ i ∈ Finset.range m, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (m - 1 - i)) /
        ((q₁ : ℝ) ^ m * (q₂ : ℝ) ^ m) := by
    intro m
    dsimp [D_fn]
    have hq1_ne : (q₁ : ℝ) ^ m ≠ 0 := by positivity
    have hq2_ne : (q₂ : ℝ) ^ m ≠ 0 := by positivity
    rw [one_div, one_div, inv_sub_inv hq1_ne hq2_ne, sub_pow_factor_real]
  have hmain_lb : ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (Y : ℝ)) ^ (k + 1) ≤ D_fn k := by
    rw [hD_eq k]
    have hsum_ge : (q₁ : ℝ) ^ (k - 1) ≤
        ∑ i ∈ Finset.range k, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (k - 1 - i) := by
      have h0_mem : 0 ∈ Finset.range k := Finset.mem_range.mpr hk_ge1
      calc (q₁ : ℝ) ^ (k - 1)
          = (q₂ : ℝ) ^ 0 * (q₁ : ℝ) ^ (k - 1 - 0) := by simp
        _ ≤ ∑ i ∈ Finset.range k, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (k - 1 - i) :=
            Finset.single_le_sum (f := fun i => (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (k - 1 - i))
              (fun i _ => by positivity) h0_mem
    have hnum_ge : ((q₂ : ℝ) - (q₁ : ℝ)) * (q₁ : ℝ) ^ (k - 1) ≤
        ((q₂ : ℝ) - (q₁ : ℝ)) * ∑ i ∈ Finset.range k, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (k - 1 - i) :=
      mul_le_mul_of_nonneg_left hsum_ge hdiff_pos.le
    have hq1k_eq : (q₁ : ℝ) ^ k = (q₁ : ℝ) ^ (k - 1) * (q₁ : ℝ) := by
      have : k = (k - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ]
    have hden_le : (q₁ : ℝ) * (q₂ : ℝ) ^ k ≤ (2 * (Y : ℝ)) ^ (k + 1) := by
      calc (q₁ : ℝ) * (q₂ : ℝ) ^ k
          ≤ (2 * (Y : ℝ)) * (2 * (Y : ℝ)) ^ k :=
            mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) hq2_ub k)
              (by positivity) (by positivity)
        _ = (2 * (Y : ℝ)) ^ (k + 1) := (pow_succ' (2 * (Y : ℝ)) k).symm
    calc ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (Y : ℝ)) ^ (k + 1)
        ≤ ((q₂ : ℝ) - (q₁ : ℝ)) / ((q₁ : ℝ) * (q₂ : ℝ) ^ k) :=
          div_le_div_of_nonneg_left hdiff_pos.le (by positivity) hden_le
      _ = (((q₂ : ℝ) - (q₁ : ℝ)) * (q₁ : ℝ) ^ (k - 1)) / ((q₁ : ℝ) ^ k * (q₂ : ℝ) ^ k) := by
          rw [hq1k_eq]
          field_simp
      _ ≤ (((q₂ : ℝ) - (q₁ : ℝ)) * ∑ i ∈ Finset.range k, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (k - 1 - i)) /
            ((q₁ : ℝ) ^ k * (q₂ : ℝ) ^ k) :=
          div_le_div_of_nonneg_right hnum_ge (by positivity)
  have hmain_abs : ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (Y : ℝ)) ^ (k + 1) ≤ |(h' j₀ : ℝ) * D_fn k| := by
    have h1 : (1 : ℝ) ≤ |(h' j₀ : ℝ)| := by
      have : 1 ≤ |h' j₀| := Int.one_le_abs hj₀_ne
      exact_mod_cast this
    rw [abs_mul, abs_of_nonneg (le_trans (by positivity) hmain_lb)]
    calc ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (Y : ℝ)) ^ (k + 1)
        ≤ 1 * D_fn k := by linarith
      _ ≤ |(h' j₀ : ℝ)| * D_fn k :=
          mul_le_mul_of_nonneg_right h1 (le_trans (by positivity) hmain_lb)
  have htail_term : ∀ j ∈ Finset.univ.erase j₀,
      |(h' j : ℝ) * D_fn (j.1 + 1)| ≤ (H : ℝ) * s * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2) := by
    intro j hj
    rcases lt_trichotomy j j₀ with hj_lt | rfl | hj_gt
    · rw [h_zero_lt j hj_lt, Int.cast_zero, zero_mul, abs_zero]
      positivity
    · exact absurd rfl (Finset.ne_of_mem_erase hj)
    · have hm_ge : k + 1 ≤ j.1 + 1 := by
        change j₀.1 < j.1 at hj_gt
        dsimp [k]; omega
      have hm_le : j.1 + 1 ≤ s := j.2
      let m := j.1 + 1
      have hD_le : D_fn m ≤ (s : ℝ) * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2) := by
        rw [hD_eq m]
        have hsum_le : ∑ i ∈ Finset.range m, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (m - 1 - i) ≤
            (m : ℝ) * (q₂ : ℝ) ^ (m - 1) := by
          calc ∑ i ∈ Finset.range m, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (m - 1 - i)
              ≤ ∑ _i ∈ Finset.range m, (q₂ : ℝ) ^ (m - 1) := by
                refine Finset.sum_le_sum fun i hi => ?_
                rw [Finset.mem_range] at hi
                have hle1 : (q₁ : ℝ) ^ (m - 1 - i) ≤ (q₂ : ℝ) ^ (m - 1 - i) :=
                  pow_le_pow_left₀ (by positivity) hq2_r.le _
                calc (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (m - 1 - i)
                    ≤ (q₂ : ℝ) ^ i * (q₂ : ℝ) ^ (m - 1 - i) :=
                      mul_le_mul_of_nonneg_left hle1 (by positivity)
                  _ = (q₂ : ℝ) ^ (i + (m - 1 - i)) := (pow_add _ _ _).symm
                  _ = (q₂ : ℝ) ^ (m - 1) := by rw [show i + (m - 1 - i) = m - 1 by omega]
            _ = (m : ℝ) * (q₂ : ℝ) ^ (m - 1) := by simp
        have hnum_le : ((q₂ : ℝ) - (q₁ : ℝ)) *
              ∑ i ∈ Finset.range m, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (m - 1 - i) ≤
            (s : ℝ) * ((q₂ : ℝ) - (q₁ : ℝ)) * (q₂ : ℝ) ^ (m - 1) := by
          have hm_r : (m : ℝ) ≤ s := by exact_mod_cast hm_le
          calc ((q₂ : ℝ) - (q₁ : ℝ)) *
                ∑ i ∈ Finset.range m, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (m - 1 - i)
              ≤ ((q₂ : ℝ) - (q₁ : ℝ)) * ((m : ℝ) * (q₂ : ℝ) ^ (m - 1)) :=
                mul_le_mul_of_nonneg_left hsum_le hdiff_pos.le
            _ ≤ ((q₂ : ℝ) - (q₁ : ℝ)) * ((s : ℝ) * (q₂ : ℝ) ^ (m - 1)) := by
                gcongr
            _ = (s : ℝ) * ((q₂ : ℝ) - (q₁ : ℝ)) * (q₂ : ℝ) ^ (m - 1) := by ring
        have hq2m_eq : (q₂ : ℝ) ^ m = (q₂ : ℝ) ^ (m - 1) * (q₂ : ℝ) := by
          have : m = (m - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ]
        have hden_ge : (Y : ℝ) ^ (k + 2) ≤ (q₁ : ℝ) ^ m * (q₂ : ℝ) := by
          have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
          calc (Y : ℝ) ^ (k + 2)
              = (Y : ℝ) ^ (k + 1) * (Y : ℝ) := by rw [pow_succ]
            _ ≤ (Y : ℝ) ^ m * (q₂ : ℝ) :=
                mul_le_mul (pow_le_pow_right₀ hY1 hm_ge) (by linarith) (by positivity) (by positivity)
            _ ≤ (q₁ : ℝ) ^ m * (q₂ : ℝ) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hq1_r.le m) (by positivity)
        calc (((q₂ : ℝ) - (q₁ : ℝ)) *
              ∑ i ∈ Finset.range m, (q₂ : ℝ) ^ i * (q₁ : ℝ) ^ (m - 1 - i)) /
                ((q₁ : ℝ) ^ m * (q₂ : ℝ) ^ m)
            ≤ ((s : ℝ) * ((q₂ : ℝ) - (q₁ : ℝ)) * (q₂ : ℝ) ^ (m - 1)) /
                ((q₁ : ℝ) ^ m * (q₂ : ℝ) ^ m) :=
              div_le_div_of_nonneg_right hnum_le (by positivity)
          _ = ((s : ℝ) * ((q₂ : ℝ) - (q₁ : ℝ))) / ((q₁ : ℝ) ^ m * (q₂ : ℝ)) := by
              rw [hq2m_eq]
              field_simp
          _ ≤ ((s : ℝ) * ((q₂ : ℝ) - (q₁ : ℝ))) / (Y : ℝ) ^ (k + 2) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hden_ge
      have hD_nn : 0 ≤ D_fn m := by
        rw [hD_eq m]; positivity
      have hj_abs : |(h' j : ℝ)| ≤ (H : ℝ) := by exact_mod_cast hh j
      rw [abs_mul, abs_of_nonneg hD_nn]
      calc |(h' j : ℝ)| * D_fn m
          ≤ (H : ℝ) * ((s : ℝ) * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2)) :=
            mul_le_mul hj_abs hD_le hD_nn (by positivity)
        _ = (H : ℝ) * s * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2) := by ring
  have htail_abs :
      |∑ j ∈ Finset.univ.erase j₀, (h' j : ℝ) * D_fn (j.1 + 1)| ≤
        ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (2 * (Y : ℝ)) ^ (k + 1)) := by
    have hcard : (Finset.univ.erase j₀ : Finset (Fin s)).card ≤ s := by
      calc (Finset.univ.erase j₀ : Finset (Fin s)).card
          ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_le_univ _
        _ = s := Finset.card_fin s
    have hsum1 : |∑ j ∈ Finset.univ.erase j₀, (h' j : ℝ) * D_fn (j.1 + 1)| ≤
        (s : ℝ) ^ 2 * H * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2) := by
      calc |∑ j ∈ Finset.univ.erase j₀, (h' j : ℝ) * D_fn (j.1 + 1)|
          ≤ ∑ j ∈ Finset.univ.erase j₀, |(h' j : ℝ) * D_fn (j.1 + 1)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.univ.erase j₀,
              (H : ℝ) * s * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2) :=
            Finset.sum_le_sum htail_term
        _ = ((Finset.univ.erase j₀ : Finset (Fin s)).card : ℝ) *
              ((H : ℝ) * s * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2)) := by simp
        _ ≤ (s : ℝ) * ((H : ℝ) * s * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        _ = (s : ℝ) ^ 2 * H * ((q₂ : ℝ) - (q₁ : ℝ)) / (Y : ℝ) ^ (k + 2) := by ring
    refine hsum1.trans ?_
    have h2_le : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (s + 1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hdom_k : 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (k + 1) ≤ (Y : ℝ) := by
      calc 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (k + 1)
          ≤ 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (s + 1) := by gcongr
        _ ≤ (Y : ℝ) := hdom
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hmul : (s : ℝ) ^ 2 * H * ((q₂ : ℝ) - (q₁ : ℝ)) * (2 * (2 * (Y : ℝ)) ^ (k + 1)) =
        (2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (k + 1)) * ((q₂ : ℝ) - (q₁ : ℝ)) * (Y : ℝ) ^ (k + 1) := by
      rw [mul_pow]; ring
    rw [hmul, show (Y : ℝ) ^ (k + 2) = (Y : ℝ) * (Y : ℝ) ^ (k + 1) by rw [pow_succ']]
    calc (2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (k + 1)) * ((q₂ : ℝ) - (q₁ : ℝ)) * (Y : ℝ) ^ (k + 1)
        ≤ (Y : ℝ) * ((q₂ : ℝ) - (q₁ : ℝ)) * (Y : ℝ) ^ (k + 1) := by
          gcongr
      _ = ((q₂ : ℝ) - (q₁ : ℝ)) * ((Y : ℝ) * (Y : ℝ) ^ (k + 1)) := by ring
  have hpow_mono : (2 * (Y : ℝ)) ^ (k + 1) ≤ (2 * (Y : ℝ)) ^ (s + 1) :=
    pow_le_pow_right₀ (by linarith [hY1]) (by omega)
  have hrev : |(h' j₀ : ℝ) * D_fn k| - |∑ j ∈ Finset.univ.erase j₀, (h' j : ℝ) * D_fn (j.1 + 1)| ≤
      |freqSum h' q₁ - freqSum h' q₂| := by
    rw [hD_split]
    exact abs_sub_abs_le_abs_add _ _
  calc ((q₂ - q₁ : ℕ) : ℝ) / (2 * (2 * (Y : ℝ)) ^ (s + 1))
      = ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (2 * (Y : ℝ)) ^ (s + 1)) := by rw [hdiff_cast]
    _ ≤ ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (2 * (Y : ℝ)) ^ (k + 1)) :=
        div_le_div_of_nonneg_left hdiff_pos.le (by positivity) (by linarith)
    _ = ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (Y : ℝ)) ^ (k + 1) -
          ((q₂ : ℝ) - (q₁ : ℝ)) / (2 * (2 * (Y : ℝ)) ^ (k + 1)) := by ring
    _ ≤ |(h' j₀ : ℝ) * D_fn k| - |∑ j ∈ Finset.univ.erase j₀, (h' j : ℝ) * D_fn (j.1 + 1)| :=
        sub_le_sub hmain_abs htail_abs
    _ ≤ |freqSum h' q₁ - freqSum h' q₂| := hrev

private lemma sum_primes_geom_e_le {X s H Y : ℕ} {P : Finset ℕ} (hs : 1 ≤ s) (hY : 1 ≤ Y)
    (hX : 0 < X) (hP : P ⊆ Finset.Ioc Y (2 * Y))
    (h' : Fin s → ℤ) (hne : h' ≠ 0) (hh : ∀ j, |h' j| ≤ (H : ℤ))
    (hdom : 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (s + 1) ≤ Y)
    (hfreq_ub : (s : ℝ) * H / Y ≤ 1 / 8)
    (α B : ℝ) (hB : 0 < B) :
    ∑ q ∈ P, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖ ≤
      max (4 * (P.card : ℝ))
        ((4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X + (P.card : ℝ) * X / (2 * B)) := by
  have hX_pos : (0 : ℝ) < X := Nat.cast_pos.mpr hX
  let m0 := round α
  by_cases hfar : 1 / 4 < |α - m0|
  · refine le_trans ?_ (le_max_left _ _)
    have hterm : ∀ q ∈ P, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖ ≤ 4 := by
      intro q hq
      have hq_mem := Finset.mem_Ioc.mp (hP hq)
      have hfq : |freqSum h' q| ≤ 1 / 8 :=
        (abs_freqSum_le hY hq_mem.1 h' hh).trans hfreq_ub
      let u := α + freqSum h' q
      let k := round u
      let θ := u - k
      have hθ_ub : |θ| ≤ 1 / 2 := abs_sub_round u
      have hak : 1 / 4 < |α - k| := by
        by_cases hkm : k = m0
        · rw [hkm]; exact hfar
        · have hdiff1 : (1 : ℝ) ≤ |(m0 : ℝ) - k| := by
            have : 1 ≤ |m0 - k| := Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hkm))
            exact_mod_cast this
          have hm0_ub : |α - m0| ≤ 1 / 2 := abs_sub_round α
          have htri : |(m0 : ℝ) - k| ≤ |α - k| + |α - m0| := by
            rw [show (m0 : ℝ) - k = (α - k) - (α - m0) by ring]
            exact abs_sub _ _
          linarith
      have hθ_lb : 1 / 8 < |θ| := by
        have htri : |α - k| - |freqSum h' q| ≤ |θ| := by
          rw [show θ = (α - k) + freqSum h' q by dsimp [θ, u]; ring]
          have := abs_sub_abs_le_abs_add (α - (k : ℝ)) (freqSum h' q)
          exact this
        linarith
      have he_eq : ∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q)) =
          ∑ n ∈ Finset.range X, e ((n : ℝ) * θ) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [show (n : ℝ) * (α + freqSum h' q) = (n : ℝ) * θ + ((n : ℤ) * k : ℤ) by
          dsimp [θ, u]; push_cast; ring, e_add_int]
      rw [he_eq]
      calc ‖∑ n ∈ Finset.range X, e ((n : ℝ) * θ)‖
          ≤ 1 / (2 * |θ|) := norm_geom_sum_e_le (by linarith) hθ_ub
        _ ≤ 1 / (2 * (1 / 8)) := by gcongr
        _ = 4 := by norm_num
    calc ∑ q ∈ P, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖
        ≤ ∑ _q ∈ P, (4 : ℝ) := Finset.sum_le_sum hterm
      _ = 4 * (P.card : ℝ) := by simp [mul_comm]
  · refine le_trans ?_ (le_max_right _ _)
    have hfar_le : |α - m0| ≤ 1 / 4 := le_of_not_gt hfar
    let θ : ℕ → ℝ := fun q => (α - m0) + freqSum h' q
    have hθ_ub : ∀ q ∈ P, |θ q| ≤ 1 / 2 := by
      intro q hq
      have hq_mem := Finset.mem_Ioc.mp (hP hq)
      have hfq : |freqSum h' q| ≤ 1 / 8 :=
        (abs_freqSum_le hY hq_mem.1 h' hh).trans hfreq_ub
      calc |θ q| ≤ |α - m0| + |freqSum h' q| := abs_add_le _ _
        _ ≤ 1 / 4 + 1 / 8 := add_le_add hfar_le hfq
        _ ≤ 1 / 2 := by norm_num
    have he_eq : ∀ q : ℕ, ∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q)) =
        ∑ n ∈ Finset.range X, e ((n : ℝ) * θ q) := by
      intro q
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show (n : ℝ) * (α + freqSum h' q) = (n : ℝ) * θ q + ((n : ℤ) * m0 : ℤ) by
        dsimp [θ]; push_cast; ring, e_add_int]
    let Near := P.filter (fun q => |θ q| < B / X)
    let Far := P.filter (fun q => ¬ |θ q| < B / X)
    have hsplit : P = Near ∪ Far := by
      ext q; simp only [Near, Far, Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint Near Far := by
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      simp only [Near, Far, Finset.mem_filter] at hq1 hq2
      exact hq2.2 hq1.2
    have hFar_bound : ∑ q ∈ Far, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖ ≤
        (P.card : ℝ) * X / (2 * B) := by
      have hterm : ∀ q ∈ Far,
          ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖ ≤ X / (2 * B) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hθ_lb : B / X ≤ |θ q| := le_of_not_gt hq.2
        rw [he_eq q]
        calc ‖∑ n ∈ Finset.range X, e ((n : ℝ) * θ q)‖
            ≤ 1 / (2 * |θ q|) := norm_geom_sum_e_le (lt_of_lt_of_le (by positivity) hθ_lb) (hθ_ub q hq.1)
          _ ≤ 1 / (2 * (B / X)) := by gcongr
          _ = (X : ℝ) / (2 * B) := by field_simp
      calc ∑ q ∈ Far, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖
          ≤ ∑ _q ∈ Far, (X : ℝ) / (2 * B) := Finset.sum_le_sum hterm
        _ = (Far.card : ℝ) * ((X : ℝ) / (2 * B)) := by simp
        _ ≤ (P.card : ℝ) * ((X : ℝ) / (2 * B)) := by
            gcongr
            exact Finset.filter_subset _ _
        _ = (P.card : ℝ) * X / (2 * B) := by ring
    have hNear_card : (Near.card : ℝ) ≤ 4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1 := by
      by_cases hne_near : Near.Nonempty
      · let q₁ := Near.min' hne_near
        let q₂ := Near.max' hne_near
        have hq1_mem : q₁ ∈ P := (Finset.mem_filter.mp (Finset.min'_mem Near hne_near)).1
        have hq2_mem : q₂ ∈ P := (Finset.mem_filter.mp (Finset.max'_mem Near hne_near)).1
        have hq1_lt : |θ q₁| < B / X := (Finset.mem_filter.mp (Finset.min'_mem Near hne_near)).2
        have hq2_lt : |θ q₂| < B / X := (Finset.mem_filter.mp (Finset.max'_mem Near hne_near)).2
        have hq1_le_q2 : q₁ ≤ q₂ := Finset.min'_le Near q₂ (Finset.max'_mem Near hne_near)
        have hNear_sub : Near ⊆ Finset.Icc q₁ q₂ := fun q hq =>
          Finset.mem_Icc.mpr ⟨Finset.min'_le Near q hq, Finset.le_max' Near q hq⟩
        have hcard_le : Near.card ≤ q₂ - q₁ + 1 := by
          calc Near.card ≤ (Finset.Icc q₁ q₂).card := Finset.card_le_card hNear_sub
            _ = q₂ + 1 - q₁ := Nat.card_Icc q₁ q₂
            _ = q₂ - q₁ + 1 := by omega
        have hdiff_bound : ((q₂ - q₁ : ℕ) : ℝ) ≤ 4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) := by
          rcases eq_or_lt_of_le hq1_le_q2 with heq | hlt
          · simp [heq]; positivity
          · have h1 := Finset.mem_Ioc.mp (hP hq1_mem)
            have h2 := Finset.mem_Ioc.mp (hP hq2_mem)
            have hsep := freq_sep hs hY h1.1 hlt h2.2 h' hne hh hdom
            have htri : |freqSum h' q₁ - freqSum h' q₂| < 2 * (B / X) := by
              rw [show freqSum h' q₁ - freqSum h' q₂ = θ q₁ - θ q₂ by dsimp [θ]; ring]
              calc |θ q₁ - θ q₂| ≤ |θ q₁| + |θ q₂| := abs_sub _ _
                _ < B / X + B / X := add_lt_add hq1_lt hq2_lt
                _ = 2 * (B / X) := by ring
            have hdiv : ((q₂ - q₁ : ℕ) : ℝ) / (2 * (2 * (Y : ℝ)) ^ (s + 1)) ≤ 2 * (B / X) :=
              hsep.trans htri.le
            rw [div_le_iff₀ (by positivity)] at hdiv
            linarith
        have hcard_r : (Near.card : ℝ) ≤ ((q₂ - q₁ : ℕ) : ℝ) + 1 := by exact_mod_cast hcard_le
        linarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne_near, Finset.card_empty, Nat.cast_zero]
        positivity
    have hNear_bound : ∑ q ∈ Near, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖ ≤
        (4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X := by
      calc ∑ q ∈ Near, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖
          ≤ ∑ q ∈ Near, (X : ℝ) := by
            refine Finset.sum_le_sum fun q _ => ?_
            rw [he_eq q]
            exact norm_geom_sum_e_le_card X (θ q)
        _ = (Near.card : ℝ) * X := by simp
        _ ≤ (4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X :=
            mul_le_mul_of_nonneg_right hNear_card hX_pos.le
    calc ∑ q ∈ P, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖
        = ∑ q ∈ Near, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖ +
            ∑ q ∈ Far, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (α + freqSum h' q))‖ := by
          rw [hsplit, Finset.sum_union hdisj]
      _ ≤ (4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X + (P.card : ℝ) * X / (2 * B) :=
          add_le_add hNear_bound hFar_bound

private lemma prod_e_eq_e_sum {ι : Type*} [DecidableEq ι] (t : Finset ι) (f : ι → ℝ) :
    ∏ j ∈ t, e (f j) = e (∑ j ∈ t, f j) := by
  induction t using Finset.induction_on with
  | empty => simp [e_zero]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, e_add]

private lemma piFinset_Icc_card (H s : ℕ) :
    (Fintype.piFinset (fun _ : Fin s => Finset.Icc (-(H : ℤ)) H)).card = (2 * H + 1) ^ s := by
  let I : Finset ℤ := Finset.Icc (-(H : ℤ)) H
  have hI_card : I.card = 2 * H + 1 := by
    dsimp [I]
    rw [Int.card_Icc]
    omega
  induction s with
  | zero =>
    have h1 : Fintype.piFinset (fun _ : Fin 0 => I) = {Fin.elim0} := by
      ext h
      simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      constructor
      · intro _; ext i; exact Fin.elim0 i
      · rintro rfl i; exact Fin.elim0 i
    rw [h1, Finset.card_singleton, pow_zero]
  | succ s ih =>
    let Fs1 := Fintype.piFinset (fun _ : Fin (s + 1) => I)
    let Fs := Fintype.piFinset (fun _ : Fin s => I)
    have hbij : Fs1.card = (I ×ˢ Fs).card := by
      refine Finset.card_bij (fun h _ => (h 0, Fin.tail h)) ?_ ?_ ?_
      · intro h hh
        rw [Fintype.mem_piFinset] at hh
        rw [Finset.mem_product, Fintype.mem_piFinset]
        exact ⟨hh 0, fun j => hh j.succ⟩
      · intro a _ b _ hab
        have h0 : a 0 = b 0 := congrArg Prod.fst hab
        have ht : Fin.tail a = Fin.tail b := congrArg Prod.snd hab
        rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, h0, ht]
      · rintro ⟨a, g⟩ hag
        rw [Finset.mem_product, Fintype.mem_piFinset] at hag
        refine ⟨Fin.cons a g, ?_, ?_⟩
        · rw [Fintype.mem_piFinset]
          refine Fin.cases hag.1 (fun j => hag.2 j)
        · ext
          · simp
          · simp
    rw [hbij, Finset.card_product, hI_card, ih, pow_succ']

private lemma piFinset_Icc_prod_sum (H s : ℕ) (f : Fin s → ℤ → ℂ) :
    ∏ j : Fin s, ∑ k ∈ Finset.Icc (-(H : ℤ)) H, f j k =
      ∑ h ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (-(H : ℤ)) H), ∏ j : Fin s, f j (h j) := by
  let I : Finset ℤ := Finset.Icc (-(H : ℤ)) H
  induction s with
  | zero =>
    have h1 : Fintype.piFinset (fun _ : Fin 0 => I) = {Fin.elim0} := by
      ext h
      simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      constructor
      · intro _; ext i; exact Fin.elim0 i
      · rintro rfl i; exact Fin.elim0 i
    change 1 = ∑ h ∈ Fintype.piFinset (fun _ : Fin 0 => I), ∏ j : Fin 0, f j (h j)
    rw [h1, Finset.sum_singleton]
    simp
  | succ s ih =>
    rw [Fin.prod_univ_succ, ih (fun j => f j.succ), Finset.sum_mul_sum]
    have hprod := (Finset.sum_product (s := I) (t := Fintype.piFinset (fun _ : Fin s => I))
      (f := fun p : ℤ × (Fin s → ℤ) => f 0 p.1 * ∏ j_1 : Fin s, f j_1.succ (p.2 j_1))).symm
    rw [hprod]
    refine Finset.sum_bij (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
    · rintro ⟨a, g⟩ hag
      rw [Finset.mem_product, Fintype.mem_piFinset] at hag
      rw [Fintype.mem_piFinset]
      exact Fin.cases hag.1 (fun j => hag.2 j)
    · rintro ⟨a₁, g₁⟩ _ ⟨a₂, g₂⟩ _ hab
      have h0 : a₁ = a₂ := by simpa using congrFun hab 0
      have ht : g₁ = g₂ := by
        ext j
        simpa using congrFun hab j.succ
      subst h0; subst ht; rfl
    · intro h hh
      rw [Fintype.mem_piFinset] at hh
      refine ⟨(h 0, Fin.tail h), Finset.mem_product.mpr ⟨hh 0, ?_⟩, ?_⟩
      · rw [Fintype.mem_piFinset]
        intro j; exact hh j.succ
      · exact Fin.cons_self_tail h
    · rintro ⟨a, g⟩ _
      simp [Fin.prod_univ_succ]

private lemma prod_T_eq_sum {s H p n : ℕ} (c : ℤ → ℂ) (T : ℝ → ℝ)
    (hT : ∀ x : ℝ, ∑ k ∈ Finset.Icc (-(H : ℤ)) H, c k * e ((k : ℝ) * x) = (T x : ℂ)) :
    ((∏ j : Fin s, T ((n : ℝ) / (p : ℝ) ^ (j.1 + 1)) : ℝ) : ℂ) =
      ∑ h ∈ Fintype.piFinset (fun _ : Fin s => Finset.Icc (-(H : ℤ)) H),
        (∏ j : Fin s, c (h j)) * e ((n : ℝ) * freqSum h p) := by
  rw [Complex.ofReal_prod]
  simp_rw [← hT]
  rw [piFinset_Icc_prod_sum H s (fun j k => c k * e ((k : ℝ) * ((n : ℝ) / (p : ℝ) ^ (j.1 + 1))))]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [prod_e_eq_e_sum]
  congr 1
  dsimp [freqSum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma one_le_prod_real {ι : Type*} [DecidableEq ι] (t : Finset ι) (f : ι → ℝ)
    (hf : ∀ j ∈ t, 1 ≤ f j) : 1 ≤ ∏ j ∈ t, f j := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact one_le_mul_of_one_le_of_one_le (hf a (Finset.mem_insert_self a s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

private lemma offdiag_second_moment_le {X s H Y : ℕ} {P : Finset ℕ}
    (hs : 1 ≤ s) (hY : 1 ≤ Y) (hX : 0 < X) (hP : P ⊆ Finset.Ioc Y (2 * Y))
    (hdom : 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (s + 1) ≤ Y)
    (hfreq_ub : (s : ℝ) * H / Y ≤ 1 / 8)
    (c : ℤ → ℂ) (T : ℝ → ℝ) (c0 B : ℝ) (hB : 0 < B) (hc0 : 0 ≤ c0)
    (hT_sum : ∀ x : ℝ, ∑ k ∈ Finset.Icc (-(H : ℤ)) H, c k * e ((k : ℝ) * x) = (T x : ℂ))
    (hT_nn : ∀ x : ℝ, 0 ≤ T x)
    (hT_ge1 : ∀ x : ℝ, Int.fract x < 1 / 2 → 1 ≤ T x)
    (hc_zero : c 0 = (c0 : ℂ))
    (hc_bound : ∀ k ∈ Finset.Icc (-(H : ℤ)) H, ‖c k‖ ≤ 2) :
    ∑ p ∈ P, ∑ q ∈ P.erase p, ∑ n ∈ Finset.range X,
        (if smallDigits p s n then (1 : ℝ) else 0) * (if smallDigits q s n then (1 : ℝ) else 0) ≤
      (P.card : ℝ) ^ 2 * X * c0 ^ (2 * s) +
        ((2 * (H : ℝ) + 1) ^ (2 * s)) * (4 : ℝ) ^ s * (P.card : ℝ) *
          (4 * (P.card : ℝ) + (4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X + (P.card : ℝ) * X / (2 * B)) := by
  let I : Finset ℤ := Finset.Icc (-(H : ℤ)) H
  let F : Finset (Fin s → ℤ) := Fintype.piFinset (fun _ : Fin s => I)
  have hind_le : ∀ p ∈ P, ∀ n : ℕ,
      (if smallDigits p s n then (1 : ℝ) else 0) ≤ ∏ j : Fin s, T ((n : ℝ) / (p : ℝ) ^ (j.1 + 1)) := by
    intro p hp n
    have hp_pos : 0 < p := lt_of_le_of_lt (by omega) (Finset.mem_Ioc.mp (hP hp)).1
    split_ifs with hsd
    · refine one_le_prod_real Finset.univ (fun j : Fin s => T ((n : ℝ) / (p : ℝ) ^ (j.1 + 1)))
        fun j _ => hT_ge1 _ ?_
      exact fract_div_pow_lt_half (r := s + 1) hp_pos (by omega : j.1 + 1 ≤ (s + 1) - 1)
        (by simpa [smallDigits] using hsd)
    · exact Finset.prod_nonneg fun j _ => hT_nn _
  have hprod_ind_le : ∀ p ∈ P, ∀ q ∈ P,
      ∑ n ∈ Finset.range X,
        (if smallDigits p s n then (1 : ℝ) else 0) * (if smallDigits q s n then (1 : ℝ) else 0) ≤
      ∑ n ∈ Finset.range X,
        (∏ j : Fin s, T ((n : ℝ) / (p : ℝ) ^ (j.1 + 1))) *
          (∏ j : Fin s, T ((n : ℝ) / (q : ℝ) ^ (j.1 + 1))) := by
    intro p hp q hq
    refine Finset.sum_le_sum fun n _ => ?_
    have h1 := hind_le p hp n
    have h2 := hind_le q hq n
    have hnnq : 0 ≤ (if smallDigits q s n then (1 : ℝ) else 0) := by positivity
    have hnn2 : 0 ≤ ∏ j : Fin s, T ((n : ℝ) / (p : ℝ) ^ (j.1 + 1)) := Finset.prod_nonneg fun j _ => hT_nn _
    exact mul_le_mul h1 h2 hnnq hnn2
  have hre_eq : ∀ p q : ℕ,
      (∑ n ∈ Finset.range X,
        (∏ j : Fin s, T ((n : ℝ) / (p : ℝ) ^ (j.1 + 1))) *
          (∏ j : Fin s, T ((n : ℝ) / (q : ℝ) ^ (j.1 + 1)))) =
      (∑ hh ∈ F ×ˢ F,
        (∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
          ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))).re := by
    intro p q
    have hc_sum : ∀ n ∈ Finset.range X,
        (((∏ j : Fin s, T ((n : ℝ) / (p : ℝ) ^ (j.1 + 1))) *
          (∏ j : Fin s, T ((n : ℝ) / (q : ℝ) ^ (j.1 + 1))) : ℝ) : ℂ) =
        ∑ hh ∈ F ×ˢ F,
          (∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
            e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q)) := by
      intro n _
      rw [Complex.ofReal_mul, prod_T_eq_sum c T hT_sum, prod_T_eq_sum c T hT_sum, Finset.sum_mul_sum]
      symm
      rw [Finset.sum_product]
      symm
      refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
      rw [mul_add, e_add]
      ring
    have h1 : (((∑ n ∈ Finset.range X,
        (∏ j : Fin s, T ((n : ℝ) / (p : ℝ) ^ (j.1 + 1))) *
          (∏ j : Fin s, T ((n : ℝ) / (q : ℝ) ^ (j.1 + 1)))) : ℝ) : ℂ) =
        ∑ hh ∈ F ×ˢ F,
          (∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
            ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q)) := by
      rw [Complex.ofReal_sum]
      rw [Finset.sum_congr rfl hc_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun hh _ => ?_
      rw [Finset.mul_sum]
    have hre := congrArg Complex.re h1
    rw [Complex.ofReal_re] at hre
    exact hre
  let z0 : Fin s → ℤ := fun _ => 0
  have hz0_mem : z0 ∈ F := by
    rw [Fintype.mem_piFinset]
    intro _
    rw [Finset.mem_Icc]
    dsimp [z0]
    omega
  have hzz_mem : (z0, z0) ∈ F ×ˢ F := Finset.mem_product.mpr ⟨hz0_mem, hz0_mem⟩
  let M_err : ℝ := 4 * (P.card : ℝ) +
    (4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X + (P.card : ℝ) * X / (2 * B)
  have hM_ge : max (4 * (P.card : ℝ))
      ((4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X + (P.card : ℝ) * X / (2 * B)) ≤ M_err := by
    refine max_le ?_ ?_
    · dsimp [M_err]; have : 0 ≤ (4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X + (P.card : ℝ) * X / (2 * B) := by positivity
      linarith
    · dsimp [M_err]; linarith [show (0 : ℝ) ≤ 4 * (P.card : ℝ) by positivity]
  have hstep1 : ∑ p ∈ P, ∑ q ∈ P.erase p, ∑ n ∈ Finset.range X,
        (if smallDigits p s n then (1 : ℝ) else 0) * (if smallDigits q s n then (1 : ℝ) else 0) ≤
      ∑ p ∈ P, ∑ q ∈ P.erase p,
        (((∏ j : Fin s, c (z0 j)) * (∏ j : Fin s, c (z0 j)) *
            ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum z0 p + freqSum z0 q))).re +
          ∑ hh ∈ (F ×ˢ F).erase (z0, z0),
            ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
              ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖) := by
    refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => ?_
    refine (hprod_ind_le p hp q (Finset.mem_of_mem_erase hq)).trans ?_
    rw [hre_eq p q, ← Finset.add_sum_erase (F ×ˢ F) _ hzz_mem, Complex.add_re]
    refine add_le_add le_rfl ?_
    rw [Complex.re_sum]
    exact Finset.sum_le_sum fun hh _ => Complex.re_le_norm _
  have hmain_sum : ∑ p ∈ P, ∑ _q ∈ P.erase p,
      ((∏ j : Fin s, c (z0 j)) * (∏ j : Fin s, c (z0 j)) *
        ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum z0 p + freqSum z0 _q))).re ≤
      (P.card : ℝ) ^ 2 * X * c0 ^ (2 * s) := by
    have hterm : ∀ p q : ℕ,
        ((∏ j : Fin s, c (z0 j)) * (∏ j : Fin s, c (z0 j)) *
          ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum z0 p + freqSum z0 q))).re =
        (X : ℝ) * c0 ^ (2 * s) := by
      intro p q
      have hz0_freq : ∀ r : ℕ, freqSum z0 r = 0 := fun r => by simp [freqSum, z0]
      rw [hz0_freq p, hz0_freq q, add_zero]
      simp only [z0, hc_zero, mul_zero, e_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        Finset.prod_const, Finset.card_fin]
      norm_cast
      rw [← pow_add, show s + s = 2 * s by omega, mul_comm]
    calc ∑ p ∈ P, ∑ q ∈ P.erase p,
          ((∏ j : Fin s, c (z0 j)) * (∏ j : Fin s, c (z0 j)) *
            ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum z0 p + freqSum z0 q))).re
        = ∑ p ∈ P, ∑ _q ∈ P.erase p, (X : ℝ) * c0 ^ (2 * s) := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hterm p q
      _ ≤ ∑ _p ∈ P, (P.card : ℝ) * ((X : ℝ) * c0 ^ (2 * s)) := by
          refine Finset.sum_le_sum fun p _ => ?_
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hle : ((P.erase p).card : ℝ) ≤ P.card := by exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
          exact mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (P.card : ℝ) ^ 2 * X * c0 ^ (2 * s) := by simp; ring
  have herr_term : ∀ hh ∈ (F ×ˢ F).erase (z0, z0),
      (∑ p ∈ P, ∑ q ∈ P.erase p,
        ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
          ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖) ≤
      (4 : ℝ) ^ s * (P.card : ℝ) * M_err := by
    intro hh hhh
    have hmem := Finset.mem_of_mem_erase hhh
    rw [Finset.mem_product] at hmem
    have hh1_bound : ∀ j : Fin s, |hh.1 j| ≤ (H : ℤ) := fun j =>
      abs_le.mpr (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hmem.1) j))
    have hh2_bound : ∀ j : Fin s, |hh.2 j| ≤ (H : ℤ) := fun j =>
      abs_le.mpr (Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hmem.2) j))
    have hcoeff1 : ‖∏ j : Fin s, c (hh.1 j)‖ ≤ (2 : ℝ) ^ s := by
      calc ‖∏ j : Fin s, c (hh.1 j)‖
          = ∏ j : Fin s, ‖c (hh.1 j)‖ := norm_prod _ _
        _ ≤ ∏ _j : Fin s, (2 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            fun j _ => hc_bound _ ((Fintype.mem_piFinset.mp hmem.1) j)
        _ = (2 : ℝ) ^ s := by simp
    have hcoeff2 : ‖∏ j : Fin s, c (hh.2 j)‖ ≤ (2 : ℝ) ^ s := by
      calc ‖∏ j : Fin s, c (hh.2 j)‖
          = ∏ j : Fin s, ‖c (hh.2 j)‖ := norm_prod _ _
        _ ≤ ∏ _j : Fin s, (2 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _)
            fun j _ => hc_bound _ ((Fintype.mem_piFinset.mp hmem.2) j)
        _ = (2 : ℝ) ^ s := by simp
    have hcoeff_prod : ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j))‖ ≤ (4 : ℝ) ^ s := by
      rw [norm_mul]
      calc ‖∏ j : Fin s, c (hh.1 j)‖ * ‖∏ j : Fin s, c (hh.2 j)‖
          ≤ (2 : ℝ) ^ s * (2 : ℝ) ^ s := mul_le_mul hcoeff1 hcoeff2 (norm_nonneg _) (by positivity)
        _ = (4 : ℝ) ^ s := by rw [← mul_pow]; norm_num
    have hnorm_pull : ∀ p q : ℕ,
        ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
          ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖ ≤
        (4 : ℝ) ^ s * ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖ := by
      intro p q
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hcoeff_prod (norm_nonneg _)
    by_cases h2_ne : hh.2 ≠ 0
    · have hne' : hh.2 ≠ 0 := h2_ne
      calc (∑ p ∈ P, ∑ q ∈ P.erase p,
            ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
              ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖)
          ≤ ∑ p ∈ P, ∑ q ∈ P.erase p,
              (4 : ℝ) ^ s * ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖ :=
            Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hnorm_pull p q
        _ ≤ ∑ p ∈ P, (4 : ℝ) ^ s *
              ∑ q ∈ P, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖ := by
            refine Finset.sum_le_sum fun p _ => ?_
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset p P) (fun _ _ _ => norm_nonneg _))
              (by positivity)
        _ ≤ ∑ _p ∈ P, (4 : ℝ) ^ s * M_err := by
            refine Finset.sum_le_sum fun p _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (sum_primes_geom_e_le hs hY hX hP hh.2 hne' hh2_bound hdom hfreq_ub (freqSum hh.1 p) B hB).trans hM_ge
        _ = (4 : ℝ) ^ s * (P.card : ℝ) * M_err := by simp; ring
    · have h2_eq : hh.2 = 0 := not_not.mp h2_ne
      have h1_ne : hh.1 ≠ 0 := by
        intro h1_eq
        have hpair : hh = (z0, z0) := Prod.ext h1_eq h2_eq
        exact (Finset.ne_of_mem_erase hhh) hpair
      have hfreq0 : ∀ q : ℕ, freqSum hh.2 q = 0 := fun q => by simp [freqSum, h2_eq]
      calc (∑ p ∈ P, ∑ q ∈ P.erase p,
            ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
              ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖)
          ≤ ∑ p ∈ P, ∑ q ∈ P.erase p,
              (4 : ℝ) ^ s * ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (0 + freqSum hh.1 p))‖ := by
            refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
            simpa [hfreq0 q] using hnorm_pull p q
        _ ≤ ∑ p ∈ P, (4 : ℝ) ^ s * (P.card : ℝ) *
              ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (0 + freqSum hh.1 p))‖ := by
            refine Finset.sum_le_sum fun p _ => ?_
            simp only [Finset.sum_const, nsmul_eq_mul]
            have hle : ((P.erase p).card : ℝ) ≤ P.card := by
              exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
            calc ((P.erase p).card : ℝ) * ((4 : ℝ) ^ s * ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (0 + freqSum hh.1 p))‖)
                ≤ (P.card : ℝ) * ((4 : ℝ) ^ s * ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (0 + freqSum hh.1 p))‖) :=
                  mul_le_mul_of_nonneg_right hle (by positivity)
              _ = (4 : ℝ) ^ s * (P.card : ℝ) * ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (0 + freqSum hh.1 p))‖ := by ring
        _ = (4 : ℝ) ^ s * (P.card : ℝ) *
              ∑ p ∈ P, ‖∑ n ∈ Finset.range X, e ((n : ℝ) * (0 + freqSum hh.1 p))‖ := by
            rw [← Finset.mul_sum]
        _ ≤ (4 : ℝ) ^ s * (P.card : ℝ) * M_err := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (sum_primes_geom_e_le hs hY hX hP hh.1 h1_ne hh1_bound hdom hfreq_ub 0 B hB).trans hM_ge
  have herr_sum : ∑ p ∈ P, ∑ q ∈ P.erase p,
      ∑ hh ∈ (F ×ˢ F).erase (z0, z0),
        ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
          ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖ ≤
      ((2 * (H : ℝ) + 1) ^ (2 * s)) * (4 : ℝ) ^ s * (P.card : ℝ) * M_err := by
    have hswap : (∑ p ∈ P, ∑ q ∈ P.erase p, ∑ hh ∈ (F ×ˢ F).erase (z0, z0),
          ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
            ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖) =
        ∑ hh ∈ (F ×ˢ F).erase (z0, z0), ∑ p ∈ P, ∑ q ∈ P.erase p,
          ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
            ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖ := by
      simp_rw [Finset.sum_comm (s := P.erase _), Finset.sum_comm (s := P)]
    rw [hswap]
    calc ∑ hh ∈ (F ×ˢ F).erase (z0, z0), ∑ p ∈ P, ∑ q ∈ P.erase p,
          ‖(∏ j : Fin s, c (hh.1 j)) * (∏ j : Fin s, c (hh.2 j)) *
            ∑ n ∈ Finset.range X, e ((n : ℝ) * (freqSum hh.1 p + freqSum hh.2 q))‖
        ≤ ∑ _hh ∈ (F ×ˢ F).erase (z0, z0), (4 : ℝ) ^ s * (P.card : ℝ) * M_err :=
          Finset.sum_le_sum herr_term
      _ = (((F ×ˢ F).erase (z0, z0)).card : ℝ) * ((4 : ℝ) ^ s * (P.card : ℝ) * M_err) := by simp
      _ ≤ ((F ×ˢ F).card : ℝ) * ((4 : ℝ) ^ s * (P.card : ℝ) * M_err) := by
          gcongr
          exact Finset.erase_subset _ _
      _ = ((2 * (H : ℝ) + 1) ^ (2 * s)) * (4 : ℝ) ^ s * (P.card : ℝ) * M_err := by
          dsimp [F]
          rw [Finset.card_product, Nat.cast_mul, piFinset_Icc_card H s, Nat.cast_pow,
            ← pow_add, show s + s = 2 * s by omega]
          push_cast
          ring
  refine hstep1.trans ?_
  simp_rw [Finset.sum_add_distrib]
  exact add_le_add hmain_sum herr_sum

private lemma bad2_asymp_W_le_exp {ε' L : ℝ} {r H : ℕ}
    (hε' : 0 < ε') (hL100 : 100 ≤ L) (hr10 : 10 ≤ r) (hH : H = r ^ 7)
    (hr_ub : (r : ℝ) ≤ 2 * L ^ (1 / 2 - ε' / 4))
    (h38 : 20 * (16 * (1 + 8 / ε') + Real.log 2048) + 100 ≤ L ^ (3 * ε' / 8)) :
    (2 * (H : ℝ) + 1) ^ (5 * r) * (2048 : ℝ) ^ r ≤ Real.exp ((1 / 4) * L ^ (1 / 2 + ε' / 4)) := by
  let α₁ := 1 / 2 - ε' / 4
  let α₀ := 1 / 2 - ε' / 8
  let α₂ := 1 / 2 + ε' / 4
  let K0 := 16 * (1 + 8 / ε') + Real.log 2048
  have hL_pos : 0 < L := by linarith
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have h2H1_le : 2 * (H : ℝ) + 1 ≤ (r : ℝ) ^ 8 := by
    subst hH
    have hr10_r : (10 : ℝ) ≤ r := by exact_mod_cast hr10
    have hr7_ge : (1 : ℝ) ≤ (r : ℝ) ^ 7 := one_le_pow₀ (by linarith)
    have hr8_eq : (r : ℝ) * (r : ℝ) ^ 7 = (r : ℝ) ^ 8 := (pow_succ' (r : ℝ) 7).symm
    calc 2 * ((r ^ 7 : ℕ) : ℝ) + 1
        = 2 * (r : ℝ) ^ 7 + 1 := by push_cast; rfl
      _ ≤ 3 * (r : ℝ) ^ 7 := by linarith
      _ ≤ (r : ℝ) * (r : ℝ) ^ 7 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (r : ℝ) ^ 8 := hr8_eq
  have hlog_r_le : Real.log (r : ℝ) ≤ 1 + (8 / ε') * L ^ (ε' / 8) := by
    have hlog_L8 : Real.log L ≤ (8 / ε') * L ^ (ε' / 8) := by
      have h1 := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hL_pos (ε' / 8))
      rw [Real.log_rpow hL_pos] at h1
      calc Real.log L
          = (8 / ε') * ((ε' / 8) * Real.log L) := by field_simp
        _ ≤ (8 / ε') * (L ^ (ε' / 8) - 1) := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (8 / ε') * L ^ (ε' / 8) := by gcongr; linarith
    have hlog_r_L : Real.log (r : ℝ) ≤ Real.log (2 * L ^ α₁) := Real.log_le_log hr_pos hr_ub
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hL_pos] at hlog_r_L
    have h1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h2 : α₁ ≤ 1 := by dsimp [α₁]; linarith
    have hlogL_nn : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    linarith [mul_le_mul_of_nonneg_right h2 hlogL_nn]
  let W : ℝ := (2 * (H : ℝ) + 1) ^ (5 * r) * (2048 : ℝ) ^ r
  have hW_pos : 0 < W := by positivity
  have hlogW : Real.log W ≤ (1 / 4) * L ^ α₂ := by
    dsimp [W]
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    have h1 : Real.log (2 * (H : ℝ) + 1) ≤ 8 * Real.log r := by
      calc Real.log (2 * (H : ℝ) + 1)
          ≤ Real.log ((r : ℝ) ^ 8) := Real.log_le_log (by positivity) h2H1_le
        _ = 8 * Real.log r := by rw [Real.log_pow]; ring
    have h2 : ((5 * r : ℕ) : ℝ) * Real.log (2 * (H : ℝ) + 1) + (r : ℝ) * Real.log 2048 ≤
        (r : ℝ) * (40 * (1 + (8 / ε') * L ^ (ε' / 8)) + Real.log 2048) := by
      have h5r : ((5 * r : ℕ) : ℝ) = 5 * (r : ℝ) := by push_cast; rfl
      rw [h5r]
      have ha := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 5 * (r : ℝ))
      have hb := mul_le_mul_of_nonneg_left hlog_r_le (by positivity : 0 ≤ 40 * (r : ℝ))
      linarith
    have hα0_eq : L ^ α₀ = L ^ α₁ * L ^ (ε' / 8) := by
      rw [← Real.rpow_add hL_pos]
      congr 1; dsimp [α₀, α₁]; ring
    have hL8_ge : 1 ≤ L ^ (ε' / 8) := Real.one_le_rpow (by linarith) (by positivity)
    have hK0_nonneg : 0 ≤ Real.log 2048 := Real.log_nonneg (by norm_num)
    have hlin : 40 * (1 + (8 / ε') * L ^ (ε' / 8)) + Real.log 2048 ≤ (5 / 2) * K0 * L ^ (ε' / 8) := by
      dsimp [K0]
      have h_mul1 : 40 ≤ 40 * L ^ (ε' / 8) := by linarith
      have h_mul2 : Real.log 2048 ≤ Real.log 2048 * L ^ (ε' / 8) := le_mul_of_one_le_right hK0_nonneg hL8_ge
      nlinarith
    have h3 : (r : ℝ) * (40 * (1 + (8 / ε') * L ^ (ε' / 8)) + Real.log 2048) ≤ 5 * K0 * L ^ α₀ := by
      calc (r : ℝ) * (40 * (1 + (8 / ε') * L ^ (ε' / 8)) + Real.log 2048)
          ≤ (2 * L ^ α₁) * ((5 / 2) * K0 * L ^ (ε' / 8)) :=
            mul_le_mul hr_ub hlin (by positivity) (by positivity)
        _ = 5 * K0 * (L ^ α₁ * L ^ (ε' / 8)) := by ring
        _ = 5 * K0 * L ^ α₀ := by rw [hα0_eq]
    have h4 : 5 * K0 * L ^ α₀ ≤ (1 / 4) * L ^ α₂ := by
      have hα2_eq : L ^ α₂ = L ^ α₀ * L ^ (3 * ε' / 8) := by
        rw [← Real.rpow_add hL_pos]
        congr 1; dsimp [α₀, α₂]; ring
      rw [hα2_eq]
      have h20 : 20 * K0 ≤ L ^ (3 * ε' / 8) := by dsimp [K0]; linarith
      nlinarith [Real.rpow_pos_of_pos hL_pos α₀]
    linarith
  calc W = Real.exp (Real.log W) := (Real.exp_log hW_pos).symm
    _ ≤ Real.exp ((1 / 4) * L ^ α₂) := Real.exp_le_exp.mpr hlogW

private lemma bad2_c0_pow_le {r s H : ℕ} {δ₀ : ℝ}
    (hr10 : 10 ≤ r) (hs_le : s ≤ r) (hH : H = r ^ 7)
    (hδ₀_pos : 0 < δ₀) (hδ₀_ub : δ₀ ≤ 1 / 8) (hr_big : 100 / δ₀ ≤ r) :
    ((1 / 2 + 2 * (1 / (r : ℝ) ^ 2)) / (1 - 1 / (4 * ((H : ℝ) + 1) * (1 / (r : ℝ) ^ 2) ^ 2))) ^ (2 * s) ≤
      (1 + δ₀ / 2) * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
  let δ : ℝ := 1 / (r : ℝ) ^ 2
  let ηF : ℝ := 1 / (4 * ((H : ℝ) + 1) * δ ^ 2)
  let c0 : ℝ := (1 / 2 + 2 * δ) / (1 - ηF)
  have hr_r : (10 : ℝ) ≤ r := by exact_mod_cast hr10
  have hηF_le : ηF ≤ 1 / (4 * (r : ℝ) ^ 3) := by
    have hden : 4 * (r : ℝ) ^ 3 ≤ 4 * ((H : ℝ) + 1) * δ ^ 2 := by
      dsimp [δ]
      subst hH
      push_cast
      field_simp
      nlinarith [show (0 : ℝ) ≤ (r : ℝ) ^ 3 by positivity]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  have hηF_half : ηF ≤ 1 / 2 := by
    refine hηF_le.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [show (0 : ℝ) ≤ (r : ℝ) ^ 2 by positivity]
  have hc0_le_half : c0 ≤ (1 / 2) * ((1 + 4 * δ) * (1 + 2 * ηF)) := by
    have hinv : 1 / (1 - ηF) ≤ 1 + 2 * ηF := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [show 0 ≤ ηF by positivity]
    calc c0 = (1 / 2) * (1 + 4 * δ) * (1 / (1 - ηF)) := by dsimp [c0]; ring
      _ ≤ (1 / 2) * (1 + 4 * δ) * (1 + 2 * ηF) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (1 / 2) * ((1 + 4 * δ) * (1 + 2 * ηF)) := by ring
  have hexp1 : (1 + 4 * δ) * (1 + 2 * ηF) ≤ Real.exp (4 * δ + 2 * ηF) := by
    calc (1 + 4 * δ) * (1 + 2 * ηF)
        ≤ Real.exp (4 * δ) * Real.exp (2 * ηF) :=
          mul_le_mul (by linarith [Real.add_one_le_exp (4 * δ)])
            (by linarith [Real.add_one_le_exp (2 * ηF)]) (by positivity) (by positivity)
      _ = Real.exp (4 * δ + 2 * ηF) := (Real.exp_add _ _).symm
  have hexp_arg_small : (2 * s : ℝ) * (4 * δ + 2 * ηF) ≤ 10 / r := by
    have hs_r' : (s : ℝ) ≤ r := by exact_mod_cast hs_le
    have h4d : 4 * δ = 4 / (r : ℝ) ^ 2 := by dsimp [δ]; ring
    have h2e : 2 * ηF ≤ 1 / (2 * (r : ℝ) ^ 3) := by
      calc 2 * ηF ≤ 2 * (1 / (4 * (r : ℝ) ^ 3)) := by linarith
        _ = 1 / (2 * (r : ℝ) ^ 3) := by ring
    have h1 : 1 / (2 * (r : ℝ) ^ 3) ≤ 1 / (r : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hsum : 4 * δ + 2 * ηF ≤ 5 / (r : ℝ) ^ 2 := by
      calc 4 * δ + 2 * ηF ≤ 4 / (r : ℝ) ^ 2 + 1 / (r : ℝ) ^ 2 := by linarith
        _ = 5 / (r : ℝ) ^ 2 := by ring
    calc (2 * s : ℝ) * (4 * δ + 2 * ηF)
        ≤ (2 * (r : ℝ)) * (5 / (r : ℝ) ^ 2) :=
          mul_le_mul (by linarith) hsum (by positivity) (by positivity)
      _ = 10 / (r : ℝ) := by field_simp; ring
  have h10r_le : 10 / (r : ℝ) ≤ δ₀ / 10 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 100 ≤ δ₀ * r := (div_le_iff₀' hδ₀_pos).mp hr_big
    linarith
  have hexp_10r : Real.exp (10 / (r : ℝ)) ≤ 1 + δ₀ / 2 := by
    have ht : 0 ≤ 10 / (r : ℝ) := by positivity
    have ht_half : 10 / (r : ℝ) ≤ 1 / 2 := by linarith
    have hexp_neg : 1 - 10 / (r : ℝ) ≤ Real.exp (-(10 / (r : ℝ))) := by
      linarith [Real.add_one_le_exp (-(10 / (r : ℝ)))]
    have hexp_inv : Real.exp (10 / (r : ℝ)) ≤ 1 / (1 - 10 / (r : ℝ)) := by
      rw [le_div_iff₀ (by linarith)]
      calc Real.exp (10 / (r : ℝ)) * (1 - 10 / (r : ℝ))
          ≤ Real.exp (10 / (r : ℝ)) * Real.exp (-(10 / (r : ℝ))) :=
            mul_le_mul_of_nonneg_left hexp_neg (by positivity)
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hquad : 1 / (1 - 10 / (r : ℝ)) ≤ 1 + 2 * (10 / (r : ℝ)) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hc0_nn : 0 ≤ c0 := by
    have : 0 < 1 - ηF := by linarith
    dsimp [c0]; positivity
  calc c0 ^ (2 * s)
      ≤ ((1 / 2) * ((1 + 4 * δ) * (1 + 2 * ηF))) ^ (2 * s) :=
        pow_le_pow_left₀ hc0_nn hc0_le_half _
    _ = ((1 + 4 * δ) * (1 + 2 * ηF)) ^ (2 * s) * (1 / 2 : ℝ) ^ (2 * s) := by
        rw [mul_pow, mul_comm]
    _ ≤ (Real.exp (4 * δ + 2 * ηF)) ^ (2 * s) * (1 / 2 : ℝ) ^ (2 * s) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hexp1 _) (by positivity)
    _ = Real.exp ((2 * s : ℝ) * (4 * δ + 2 * ηF)) * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        · push_cast; ring
        · rw [one_div_pow, zpow_neg, show (2 * (s : ℤ)) = ((2 * s : ℕ) : ℤ) by push_cast; ring,
            zpow_natCast, inv_eq_one_div]
    _ ≤ Real.exp (10 / (r : ℝ)) * (2 : ℝ) ^ (-(2 * (s : ℤ))) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp_arg_small) (by positivity)
    _ ≤ (1 + δ₀ / 2) * (2 : ℝ) ^ (-(2 * (s : ℤ))) :=
        mul_le_mul_of_nonneg_right hexp_10r (by positivity)

private lemma bad2_moment_finish {X s : ℕ} {P : Finset ℕ} {Bad Good : Finset ℕ} {δ₀ η : ℝ}
    (hX_pos : 0 < X) (hP_pos : (0 : ℝ) < P.card) (hδ₀_pos : 0 < δ₀) (hδ₀_ub : δ₀ ≤ 1 / 8)
    (h3δ₀_lt : 3 * δ₀ < η) (hGood_sub : Good ⊆ Finset.range X) (hBad_sub : Bad ⊆ Finset.range X)
    (hDisj : Disjoint Good Bad)
    (Z : ℕ → ℝ) (hZ_zero : ∀ n ∈ Finset.range X, n ∉ Good → Z n = 0)
    (hM1 : (1 - δ₀) * (X : ℝ) * (P.card : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) ≤ ∑ n ∈ Finset.range X, Z n)
    (hM2 : ∑ n ∈ Finset.range X, Z n ^ 2 ≤
      (1 + δ₀) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ)))) :
    (Bad.card : ℝ) / (X : ℝ) < η := by
  have hX_rpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  have hsum_Good : ∑ n ∈ Finset.range X, Z n = ∑ n ∈ Good, Z n := by
    rw [← Finset.sum_subset hGood_sub]
    intro n hn hnot
    exact hZ_zero n hn hnot
  have hM2_Good : ∑ n ∈ Good, Z n ^ 2 ≤ ∑ n ∈ Finset.range X, Z n ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hGood_sub (fun _ _ _ => sq_nonneg _)
  have hCS := sq_sum_le_card_mul_sum_sq (s := Good) (f := Z)
  have hLHS_ge : ((1 - δ₀) * (X : ℝ) * (P.card : ℝ) * (2 : ℝ) ^ (-(s : ℤ))) ^ 2 ≤
      (∑ n ∈ Good, Z n) ^ 2 := by
    rw [← hsum_Good]
    exact pow_le_pow_left₀
      (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hX_rpos.le) hP_pos.le) (by positivity)) hM1 2
  have hDen_pos : 0 < (1 + δ₀) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
    positivity
  have hRHS_le : (Good.card : ℝ) * ∑ n ∈ Good, Z n ^ 2 ≤
      (Good.card : ℝ) * ((1 + δ₀) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ)))) :=
    mul_le_mul_of_nonneg_left (hM2_Good.trans hM2) (Nat.cast_nonneg _)
  have hGood_lb_mul : (1 - δ₀) ^ 2 * (X : ℝ) ≤ (1 + δ₀) * (Good.card : ℝ) := by
    have hpow2 : ((2 : ℝ) ^ (-(s : ℤ))) ^ 2 = (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
      rw [← zpow_natCast, ← zpow_mul]; congr 1; omega
    have hcombined : ((1 - δ₀) ^ 2 * (X : ℝ)) * ((X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ)))) ≤
        ((1 + δ₀) * (Good.card : ℝ)) * ((X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ)))) := by
      calc ((1 - δ₀) ^ 2 * (X : ℝ)) * ((X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))))
          = ((1 - δ₀) * (X : ℝ) * (P.card : ℝ) * (2 : ℝ) ^ (-(s : ℤ))) ^ 2 := by
            rw [← hpow2]; ring
        _ ≤ (Good.card : ℝ) * ((1 + δ₀) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ)))) :=
            hLHS_ge.trans (hCS.trans hRHS_le)
        _ = ((1 + δ₀) * (Good.card : ℝ)) * ((X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ)))) := by ring
    exact le_of_mul_le_mul_right hcombined (by positivity)
  have hGood_ge : (1 - 3 * δ₀) * (X : ℝ) ≤ Good.card := by
    have hquad : (1 - 3 * δ₀) * (1 + δ₀) ≤ (1 - δ₀) ^ 2 := by nlinarith
    have h1 : (1 + δ₀) * ((1 - 3 * δ₀) * (X : ℝ)) ≤ (1 + δ₀) * (Good.card : ℝ) := by
      calc (1 + δ₀) * ((1 - 3 * δ₀) * (X : ℝ))
          = ((1 - 3 * δ₀) * (1 + δ₀)) * (X : ℝ) := by ring
        _ ≤ (1 - δ₀) ^ 2 * (X : ℝ) := mul_le_mul_of_nonneg_right hquad hX_rpos.le
        _ ≤ (1 + δ₀) * (Good.card : ℝ) := hGood_lb_mul
    exact le_of_mul_le_mul_left h1 (by linarith)
  have hcard_sum : Good.card + Bad.card ≤ X := by
    rw [← Finset.card_union_of_disjoint hDisj]
    exact (Finset.card_le_card (Finset.union_subset hGood_sub hBad_sub)).trans_eq (Finset.card_range X)
  have hBad_le : (Bad.card : ℝ) ≤ 3 * δ₀ * (X : ℝ) := by
    have : (Good.card : ℝ) + (Bad.card : ℝ) ≤ (X : ℝ) := by exact_mod_cast hcard_sum
    linarith
  rw [div_lt_iff₀ hX_rpos]
  calc (Bad.card : ℝ) ≤ 3 * δ₀ * (X : ℝ) := hBad_le
    _ < η * (X : ℝ) := mul_lt_mul_of_pos_right h3δ₀_lt hX_rpos

open Classical in
private noncomputable def bad2Finset (X : ℕ) (ε' : ℝ) : Finset ℕ :=
  (Finset.range X).filter (fun n =>
    ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Real.exp (Real.log X ^ (1 / 2 + ε' / 2)) →
      p ∣ Nat.centralBinom n)

private lemma mem_bad2Finset {X n : ℕ} {ε' : ℝ} :
    n ∈ bad2Finset X ε' ↔
      n < X ∧ ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Real.exp (Real.log X ^ (1 / 2 + ε' / 2)) →
        p ∣ Nat.centralBinom n := by
  classical
  simp [bad2Finset, Finset.mem_filter, Finset.mem_range]

private lemma bad2_log2Y_ub {Y : ℕ} {A : ℝ} (hA : 10000 ≤ A) (hY_pos : 0 < Y)
    (hY_le : (Y : ℝ) ≤ 2 * Real.exp (2 * A)) :
    4 * Real.log (2 * (Y : ℝ)) ≤ Real.exp ((1 / 8) * A) := by
  have h2Y_pos : (0 : ℝ) < 2 * Y := by positivity
  have h1 : Real.log (2 * (Y : ℝ)) ≤ Real.log (4 * Real.exp (2 * A)) :=
    Real.log_le_log h2Y_pos (by linarith)
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9]
  have hu : ((1 / 8 : ℝ) * A) ^ 2 / 4 ≤ Real.exp ((1 / 8) * A) := by
    have hhalf : 1 + ((1 / 8 : ℝ) * A) / 2 ≤ Real.exp (((1 / 8 : ℝ) * A) / 2) := by
      linarith [Real.add_one_le_exp (((1 / 8 : ℝ) * A) / 2)]
    have hsq : (1 + ((1 / 8 : ℝ) * A) / 2) ^ 2 ≤ (Real.exp (((1 / 8 : ℝ) * A) / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hhalf 2
    have hexp_sq : (Real.exp (((1 / 8 : ℝ) * A) / 2)) ^ 2 = Real.exp ((1 / 8) * A) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have hpoly : ((1 / 8 : ℝ) * A) ^ 2 / 4 ≤ (1 + ((1 / 8 : ℝ) * A) / 2) ^ 2 := by nlinarith
    linarith
  nlinarith

private lemma bad2_hp_pow_ratio {X r s Y : ℕ} {P : Finset ℕ} {W δ₀ : ℝ}
    (hX_pos : 0 < X) (hs_r : s + 1 = r)
    (hY_le_2pow : (Y : ℝ) ≤ 2 * (2 * (X : ℝ)) ^ (1 / (r : ℝ)))
    (hW_ge_4r : 4 * (4 : ℝ) ^ r ≤ W)
    (hW_ratio_Y : W * (1000 / δ₀) ≤ Y)
    (hP_sub : P ⊆ Finset.Ioc Y (2 * Y))
    (hW_pos : 0 < W) (hδ₀_pos : 0 < δ₀) :
    ∀ p ∈ P, (p : ℝ) ^ s / (X : ℝ) ≤ δ₀ := by
  intro p hp
  have hX_rpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hY_pos : (0 : ℝ) < Y := lt_of_lt_of_le (by positivity) hW_ratio_Y
  have hp_ub : (p : ℝ) ≤ 2 * Y := by exact_mod_cast (Finset.mem_Ioc.mp (hP_sub hp)).2
  have hpow_2Y : (2 * (Y : ℝ)) ^ s ≤ 4 ^ s * ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ s := by
    calc (2 * (Y : ℝ)) ^ s
        ≤ (4 * (2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ s :=
          pow_le_pow_left₀ (by positivity) (by linarith) s
      _ = 4 ^ s * ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ s := mul_pow _ _ s
  have hpow_X : ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ s =
      (2 * (X : ℝ)) / ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) := by
    rw [← Real.rpow_natCast ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) s, ← Real.rpow_mul (by positivity)]
    rw [eq_div_iff (Real.rpow_pos_of_pos (by positivity) _).ne']
    rw [← Real.rpow_add (by positivity)]
    have hs1 : (s : ℝ) + 1 = r := by exact_mod_cast hs_r
    have hexp : 1 / (r : ℝ) * (s : ℝ) + 1 / (r : ℝ) = 1 := by
      calc 1 / (r : ℝ) * (s : ℝ) + 1 / (r : ℝ)
          = ((s : ℝ) + 1) / (r : ℝ) := by ring
        _ = (r : ℝ) / (r : ℝ) := by rw [hs1]
        _ = 1 := div_self hr_pos.ne'
    rw [hexp, Real.rpow_one]
  have hps_le : (p : ℝ) ^ s ≤ 4 * (4 : ℝ) ^ r * (X : ℝ) / (Y : ℝ) := by
    have h4s_le : (4 : ℝ) ^ s ≤ (4 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
    have hXr_lb : (Y : ℝ) / 2 ≤ (2 * (X : ℝ)) ^ (1 / (r : ℝ)) := by linarith
    calc (p : ℝ) ^ s
        ≤ (2 * (Y : ℝ)) ^ s := pow_le_pow_left₀ (by positivity) hp_ub s
      _ ≤ 4 ^ s * ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ s := hpow_2Y
      _ = 4 ^ s * (2 * (X : ℝ)) / ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) := by rw [hpow_X]; ring
      _ ≤ (4 : ℝ) ^ r * (2 * (X : ℝ)) / ((Y : ℝ) / 2) := by
          refine div_le_div₀ (by positivity) (by gcongr) (by positivity) hXr_lb
      _ = 4 * (4 : ℝ) ^ r * (X : ℝ) / (Y : ℝ) := by ring
  calc (p : ℝ) ^ s / (X : ℝ)
      ≤ (4 * (4 : ℝ) ^ r * (X : ℝ) / (Y : ℝ)) / (X : ℝ) :=
        div_le_div_of_nonneg_right hps_le hX_rpos.le
    _ = 4 * (4 : ℝ) ^ r / (Y : ℝ) := by field_simp
    _ ≤ W / (Y : ℝ) := div_le_div_of_nonneg_right hW_ge_4r hY_pos.le
    _ ≤ δ₀ := by
        rw [div_le_iff₀ hY_pos]
        have hmul : W * (1000 / δ₀) * δ₀ ≤ (Y : ℝ) * δ₀ :=
          mul_le_mul_of_nonneg_right hW_ratio_Y hδ₀_pos.le
        have hsimp : W * (1000 / δ₀) * δ₀ = 1000 * W := by field_simp
        rw [hsimp] at hmul
        linarith

private lemma bad2_C_lb {X s Y : ℕ} {P : Finset ℕ} {δ₀ : ℝ}
    (hX_pos : 0 < X) (hP_sub : P ⊆ Finset.Ioc Y (2 * Y))
    (hδ₀_ub : δ₀ ≤ 1 / 8) (hp_pow_ratio : ∀ p ∈ P, (p : ℝ) ^ s / (X : ℝ) ≤ δ₀) :
    ∀ p ∈ P, (1 - δ₀) * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) ≤
      (((Finset.range X).filter (smallDigits p s)).card : ℝ) := by
  intro p hp
  have hX_rpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  have hp_pos : 0 < p := lt_of_le_of_lt (by omega) (Finset.mem_Ioc.mp (hP_sub hp)).1
  have hcard := (card_smallDigits_range_bounds (p := p) (s := s) (X := X) hp_pos).1
  have hcard_r : ((X / p ^ s : ℕ) : ℝ) * (((p + 1) / 2 : ℕ) : ℝ) ^ s ≤
      (((Finset.range X).filter (smallDigits p s)).card : ℝ) := by exact_mod_cast hcard
  have hQ_lb : (X : ℝ) / (p : ℝ) ^ s - 1 ≤ ((X / p ^ s : ℕ) : ℝ) := by
    have hdm : p ^ s * (X / p ^ s) + X % p ^ s = X := Nat.div_add_mod X (p ^ s)
    have hrm : X % p ^ s < p ^ s := Nat.mod_lt X (pow_pos hp_pos s)
    have hlt_nat : X < (X / p ^ s + 1) * p ^ s := by
      have hmul_eq : (X / p ^ s + 1) * p ^ s = p ^ s * (X / p ^ s) + p ^ s := by ring
      omega
    have hlt_r : (X : ℝ) < (((X / p ^ s : ℕ) : ℝ) + 1) * (p : ℝ) ^ s := by exact_mod_cast hlt_nat
    rw [sub_le_iff_le_add, div_le_iff₀ (by positivity)]
    exact hlt_r.le
  have hp_half : (p : ℝ) / 2 ≤ ((p + 1) / 2 : ℕ) := by
    have hnat : p ≤ 2 * ((p + 1) / 2) := by omega
    have hr : (p : ℝ) ≤ 2 * (((p + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hpow_half : (p : ℝ) ^ s * (2 : ℝ) ^ (-(s : ℤ)) ≤ (((p + 1) / 2 : ℕ) : ℝ) ^ s := by
    calc (p : ℝ) ^ s * (2 : ℝ) ^ (-(s : ℤ))
        = ((p : ℝ) / 2) ^ s := by rw [div_pow, zpow_neg, zpow_natCast, div_eq_mul_inv]
      _ ≤ (((p + 1) / 2 : ℕ) : ℝ) ^ s := pow_le_pow_left₀ (by positivity) hp_half s
  have hXps : 0 ≤ (X : ℝ) / (p : ℝ) ^ s - 1 := by
    have h1 := hp_pow_ratio p hp
    have hps_le_X : (p : ℝ) ^ s ≤ (X : ℝ) := by
      rw [div_le_iff₀ hX_rpos] at h1
      have : δ₀ * (X : ℝ) ≤ (X : ℝ) := mul_le_of_le_one_left hX_rpos.le (by linarith)
      linarith
    rw [sub_nonneg, le_div_iff₀ (by positivity)]
    linarith
  calc (1 - δ₀) * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ))
      ≤ (1 - (p : ℝ) ^ s / (X : ℝ)) * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) := by
        gcongr; exact hp_pow_ratio p hp
    _ = ((X : ℝ) / (p : ℝ) ^ s - 1) * ((p : ℝ) ^ s * (2 : ℝ) ^ (-(s : ℤ))) := by field_simp
    _ ≤ ((X / p ^ s : ℕ) : ℝ) * (((p + 1) / 2 : ℕ) : ℝ) ^ s :=
        mul_le_mul hQ_lb hpow_half (by positivity) (by positivity)
    _ ≤ (((Finset.range X).filter (smallDigits p s)).card : ℝ) := hcard_r

private lemma bad2_C_ub {X r s Y H : ℕ} {P : Finset ℕ} {W δ₀ : ℝ}
    (hX_pos : 0 < X) (hs_r : s + 1 = r)
    (hW_def : W = (2 * (H : ℝ) + 1) ^ (5 * r) * (2048 : ℝ) ^ r)
    (hW_le_Y : W ≤ Y) (hP_sub : P ⊆ Finset.Ioc Y (2 * Y))
    (hδ₀_ub : δ₀ ≤ 1 / 8) (hp_pow_ratio : ∀ p ∈ P, (p : ℝ) ^ s / (X : ℝ) ≤ δ₀) :
    ∀ p ∈ P, (((Finset.range X).filter (smallDigits p s)).card : ℝ) ≤
      6 * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) := by
  intro p hp
  have hX_rpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  have hp_gt_Y : (Y : ℝ) < p := by exact_mod_cast (Finset.mem_Ioc.mp (hP_sub hp)).1
  have hp_pos : 0 < p := lt_of_le_of_lt (by omega) (Finset.mem_Ioc.mp (hP_sub hp)).1
  have hcard := (card_smallDigits_range_bounds (p := p) (s := s) (X := X) hp_pos).2
  have hcard_r : (((Finset.range X).filter (smallDigits p s)).card : ℝ) ≤
      (((X / p ^ s : ℕ) : ℝ) + 1) * (((p + 1) / 2 : ℕ) : ℝ) ^ s := by exact_mod_cast hcard
  have hQ_ub : ((X / p ^ s : ℕ) : ℝ) + 1 ≤ 2 * ((X : ℝ) / (p : ℝ) ^ s) := by
    have hQ_le : ((X / p ^ s : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) ^ s := by
      rw [le_div_iff₀ (by positivity)]
      exact_mod_cast Nat.div_mul_le_self X (p ^ s)
    have h1 : (p : ℝ) ^ s ≤ (X : ℝ) := by
      have := hp_pow_ratio p hp
      rw [div_le_iff₀ hX_rpos] at this
      have hdx : δ₀ * (X : ℝ) ≤ (X : ℝ) := mul_le_of_le_one_left hX_rpos.le (by linarith)
      linarith
    have h2 : 1 ≤ (X : ℝ) / (p : ℝ) ^ s := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hhalf_ub : (((p + 1) / 2 : ℕ) : ℝ) ≤ (p : ℝ) * (1 / 2) * (1 + 1 / (p : ℝ)) := by
    have hnat : 2 * ((p + 1) / 2) ≤ p + 1 := Nat.mul_div_le (p + 1) 2
    have hr : 2 * (((p + 1) / 2 : ℕ) : ℝ) ≤ (p : ℝ) + 1 := by exact_mod_cast hnat
    have hEq : (p : ℝ) * (1 / 2) * (1 + 1 / (p : ℝ)) = ((p : ℝ) + 1) / 2 := by
      have hp0 : (p : ℝ) ≠ 0 := by positivity
      field_simp
    linarith
  have hexp1 : (1 + 1 / (p : ℝ)) ^ s ≤ 3 := by
    have h1 : 1 + 1 / (p : ℝ) ≤ Real.exp (1 / (p : ℝ)) := by linarith [Real.add_one_le_exp (1 / (p : ℝ))]
    have h2 : (1 + 1 / (p : ℝ)) ^ s ≤ Real.exp ((s : ℝ) / (p : ℝ)) := by
      calc (1 + 1 / (p : ℝ)) ^ s ≤ (Real.exp (1 / (p : ℝ))) ^ s := pow_le_pow_left₀ (by positivity) h1 s
        _ = Real.exp ((s : ℝ) * (1 / (p : ℝ))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp ((s : ℝ) / (p : ℝ)) := by ring_nf
    have hsp_le : (s : ℝ) / (p : ℝ) ≤ 1 := by
      have hs_r' : (s : ℝ) ≤ r := by exact_mod_cast (by omega : s ≤ r)
      have hr_Y : (r : ℝ) ≤ Y := by
        have hr_le_W : (r : ℝ) ≤ W := by
          have h1r : (r : ℝ) ≤ (2048 : ℝ) ^ r := by
            calc (r : ℝ) ≤ (2 : ℝ) ^ r := by exact_mod_cast Nat.lt_two_pow_self.le
              _ ≤ (2048 : ℝ) ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
          have h2r : (1 : ℝ) ≤ (2 * (H : ℝ) + 1) ^ (5 * r) :=
            one_le_pow₀ (by linarith [show (0 : ℝ) ≤ H by positivity])
          rw [hW_def]
          calc (r : ℝ) ≤ 1 * (2048 : ℝ) ^ r := by linarith
            _ ≤ (2 * (H : ℝ) + 1) ^ (5 * r) * (2048 : ℝ) ^ r :=
                mul_le_mul_of_nonneg_right h2r (by positivity)
        exact hr_le_W.trans hW_le_Y
      rw [div_le_one (by positivity)]
      linarith
    calc (1 + 1 / (p : ℝ)) ^ s ≤ Real.exp ((s : ℝ) / (p : ℝ)) := h2
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsp_le
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hpow_ub : (((p + 1) / 2 : ℕ) : ℝ) ^ s ≤ 3 * (p : ℝ) ^ s * (2 : ℝ) ^ (-(s : ℤ)) := by
    calc (((p + 1) / 2 : ℕ) : ℝ) ^ s
        ≤ ((p : ℝ) * (1 / 2) * (1 + 1 / (p : ℝ))) ^ s := pow_le_pow_left₀ (by positivity) hhalf_ub s
      _ = (1 + 1 / (p : ℝ)) ^ s * (p : ℝ) ^ s * (1 / 2 : ℝ) ^ s := by rw [mul_pow, mul_pow]; ring
      _ ≤ 3 * (p : ℝ) ^ s * (2 : ℝ) ^ (-(s : ℤ)) := by
          rw [zpow_neg, zpow_natCast, one_div_pow, inv_eq_one_div]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp1 (by positivity)) (by positivity)
  calc (((Finset.range X).filter (smallDigits p s)).card : ℝ)
      ≤ (((X / p ^ s : ℕ) : ℝ) + 1) * (((p + 1) / 2 : ℕ) : ℝ) ^ s := hcard_r
    _ ≤ (2 * ((X : ℝ) / (p : ℝ) ^ s)) * (3 * (p : ℝ) ^ s * (2 : ℝ) ^ (-(s : ℤ))) :=
        mul_le_mul hQ_ub hpow_ub (by positivity) (by positivity)
    _ = 6 * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) := by field_simp; ring

private lemma bad2_hoff_err_le {X r s Y H : ℕ} {P : Finset ℕ} {W δ₀ : ℝ}
    (hX_pos : 0 < X) (hr_ge : 10 ≤ r) (hr_big : 100 / δ₀ ≤ (r : ℝ))
    (hs_r : s + 1 = r) (hH : H = r ^ 7)
    (hY_le_2pow : (Y : ℝ) ≤ 2 * (2 * (X : ℝ)) ^ (1 / (r : ℝ)))
    (hW_def : W = (2 * (H : ℝ) + 1) ^ (5 * r) * (2048 : ℝ) ^ r)
    (hX_ge_W : W * (1000 / δ₀) ≤ X) (hP_ge_W : W * (1000 / δ₀) ≤ P.card)
    (hδ₀_pos : 0 < δ₀) :
    let B : ℝ := ((2 * (H : ℝ) + 1) ^ (3 * r)) * (16 : ℝ) ^ r
    ((2 * (H : ℝ) + 1) ^ (2 * s)) * (4 : ℝ) ^ s * (P.card : ℝ) *
      (4 * (P.card : ℝ) + (4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X + (P.card : ℝ) * X / (2 * B)) ≤
    (δ₀ / 4) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
  intro B
  have hX_rpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hW_pos : 0 < W := by rw [hW_def]; positivity
  have hP_pos : (0 : ℝ) < P.card := lt_of_lt_of_le (by positivity) hP_ge_W
  have hH_ge1 : 1 ≤ H := by rw [hH]; exact Nat.one_le_pow 7 r (by omega)
  have h2H1_ge1 : 1 ≤ 2 * H + 1 := by omega
  have hB_pos : 0 < B := by positivity
  let C := ((2 * (H : ℝ) + 1) ^ (2 * s)) * (16 : ℝ) ^ s
  have hC_le : C ≤ ((2 * (H : ℝ) + 1) ^ (2 * r)) * (16 : ℝ) ^ r := by
    dsimp [C]
    exact mul_le_mul (pow_le_pow_right₀ (by exact_mod_cast h2H1_ge1) (by omega))
      (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity) (by positivity)
  have h4C_le_W : 4 * C ≤ W := by
    rw [hW_def]
    have h1 : (2 * (H : ℝ) + 1) ^ (2 * r) ≤ (2 * (H : ℝ) + 1) ^ (5 * r) :=
      pow_le_pow_right₀ (by exact_mod_cast h2H1_ge1) (by omega)
    have h2 : 4 * (16 : ℝ) ^ r ≤ (2048 : ℝ) ^ r := by
      calc 4 * (16 : ℝ) ^ r ≤ (4 : ℝ) ^ r * (16 : ℝ) ^ r := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact le_self_pow₀ (by norm_num) (by omega)
        _ = (64 : ℝ) ^ r := by rw [← mul_pow]; norm_num
        _ ≤ (2048 : ℝ) ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
    calc 4 * C ≤ 4 * (((2 * (H : ℝ) + 1) ^ (2 * r)) * (16 : ℝ) ^ r) := by linarith
      _ = (2 * (H : ℝ) + 1) ^ (2 * r) * (4 * (16 : ℝ) ^ r) := by ring
      _ ≤ (2 * (H : ℝ) + 1) ^ (5 * r) * (2048 : ℝ) ^ r := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hterm1 : 4 * C / (X : ℝ) ≤ δ₀ / 12 := by
    calc 4 * C / (X : ℝ) ≤ W / (X : ℝ) := div_le_div_of_nonneg_right h4C_le_W hX_rpos.le
      _ ≤ W / (W * (1000 / δ₀)) := div_le_div_of_nonneg_left (by positivity) (by positivity) hX_ge_W
      _ = δ₀ / 1000 := by field_simp
      _ ≤ δ₀ / 12 := by linarith
  have h2Yr_le : (2 * (Y : ℝ)) ^ (s + 1) ≤ 2 * (4 : ℝ) ^ r * (X : ℝ) := by
    rw [hs_r]
    have h1 : (2 * (Y : ℝ)) ^ r ≤ (4 * (2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ r :=
      pow_le_pow_left₀ (by positivity) (by linarith) r
    have h2 : ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ r = 2 * (X : ℝ) := by
      rw [← Real.rpow_natCast ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) r, ← Real.rpow_mul (by positivity)]
      simp [hr_pos.ne']
    calc (2 * (Y : ℝ)) ^ r ≤ (4 : ℝ) ^ r * ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ r := by rwa [← mul_pow]
      _ = 2 * (4 : ℝ) ^ r * (X : ℝ) := by rw [h2]; ring
  have hterm2 : C * (4 * (B / (X : ℝ)) * (2 * (Y : ℝ)) ^ (s + 1) + 1) / (P.card : ℝ) ≤ δ₀ / 12 := by
    have hinner : 4 * (B / (X : ℝ)) * (2 * (Y : ℝ)) ^ (s + 1) + 1 ≤
        9 * (2 * (H : ℝ) + 1) ^ (3 * r) * (64 : ℝ) ^ r := by
      have h1 : 4 * (B / (X : ℝ)) * (2 * (Y : ℝ)) ^ (s + 1) ≤
          4 * (B / (X : ℝ)) * (2 * (4 : ℝ) ^ r * (X : ℝ)) :=
        mul_le_mul_of_nonneg_left h2Yr_le (by positivity)
      have h2 : 4 * (B / (X : ℝ)) * (2 * (4 : ℝ) ^ r * (X : ℝ)) =
          8 * (2 * (H : ℝ) + 1) ^ (3 * r) * (64 : ℝ) ^ r := by
        dsimp [B]
        rw [show (64 : ℝ) ^ r = (16 : ℝ) ^ r * (4 : ℝ) ^ r by rw [← mul_pow]; norm_num]
        field_simp [hX_rpos.ne']; ring
      have h3 : (1 : ℝ) ≤ (2 * (H : ℝ) + 1) ^ (3 * r) * (64 : ℝ) ^ r := by
        have ha : (1 : ℝ) ≤ (2 * (H : ℝ) + 1) ^ (3 * r) :=
          one_le_pow₀ (by linarith [show (0 : ℝ) ≤ H by positivity])
        have hb : (1 : ℝ) ≤ (64 : ℝ) ^ r := one_le_pow₀ (by norm_num)
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ (2 * (H : ℝ) + 1) ^ (3 * r) * (64 : ℝ) ^ r :=
              mul_le_mul ha hb (by positivity) (by positivity)
      linarith
    have hprod9 : C * (4 * (B / (X : ℝ)) * (2 * (Y : ℝ)) ^ (s + 1) + 1) ≤ 9 * W := by
      calc C * (4 * (B / (X : ℝ)) * (2 * (Y : ℝ)) ^ (s + 1) + 1)
          ≤ (((2 * (H : ℝ) + 1) ^ (2 * r)) * (16 : ℝ) ^ r) * (9 * (2 * (H : ℝ) + 1) ^ (3 * r) * (64 : ℝ) ^ r) :=
            mul_le_mul hC_le hinner (by positivity) (by positivity)
        _ = 9 * ((2 * (H : ℝ) + 1) ^ (5 * r) * (1024 : ℝ) ^ r) := by
            rw [show 5 * r = 2 * r + 3 * r by omega, pow_add,
              show (1024 : ℝ) ^ r = (16 : ℝ) ^ r * (64 : ℝ) ^ r by rw [← mul_pow]; norm_num]
            ring
        _ ≤ 9 * W := by
            rw [hW_def]
            gcongr
            norm_num
    calc C * (4 * (B / (X : ℝ)) * (2 * (Y : ℝ)) ^ (s + 1) + 1) / (P.card : ℝ)
        ≤ 9 * W / (P.card : ℝ) := div_le_div_of_nonneg_right hprod9 hP_pos.le
      _ ≤ 9 * W / (W * (1000 / δ₀)) := div_le_div_of_nonneg_left (by positivity) (by positivity) hP_ge_W
      _ = 9 * δ₀ / 1000 := by field_simp
      _ ≤ δ₀ / 12 := by linarith
  have hterm3 : C / (2 * B) ≤ δ₀ / 12 := by
    have hpow_ge : 100 / δ₀ ≤ (2 * (H : ℝ) + 1) ^ r := by
      have h1 : (r : ℝ) ≤ 2 * (H : ℝ) + 1 := by
        have : r ≤ H := by rw [hH]; exact Nat.le_self_pow (by norm_num) r
        exact_mod_cast (by omega : r ≤ 2 * H + 1)
      have h2 : 2 * (H : ℝ) + 1 ≤ (2 * (H : ℝ) + 1) ^ r :=
        le_self_pow₀ (by exact_mod_cast h2H1_ge1) (by omega)
      exact hr_big.trans (h1.trans h2)
    calc C / (2 * B)
        ≤ (((2 * (H : ℝ) + 1) ^ (2 * r)) * (16 : ℝ) ^ r) / (2 * (((2 * (H : ℝ) + 1) ^ (3 * r)) * (16 : ℝ) ^ r)) :=
          div_le_div_of_nonneg_right hC_le (by positivity)
      _ = 1 / (2 * (2 * (H : ℝ) + 1) ^ r) := by
          rw [show 3 * r = 2 * r + r by omega, pow_add]
          field_simp
      _ ≤ 1 / (2 * (100 / δ₀)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
      _ = δ₀ / 200 := by field_simp; norm_num
      _ ≤ δ₀ / 12 := by linarith
  have hfactor :
      ((2 * (H : ℝ) + 1) ^ (2 * s)) * (4 : ℝ) ^ s * (P.card : ℝ) *
        (4 * (P.card : ℝ) + (4 * (B / (X : ℝ)) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * (X : ℝ) + (P.card : ℝ) * (X : ℝ) / (2 * B)) =
      (4 * C / (X : ℝ) + C * (4 * (B / (X : ℝ)) * (2 * (Y : ℝ)) ^ (s + 1) + 1) / (P.card : ℝ) + C / (2 * B)) *
        ((X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ)))) := by
    have h4s_eq : (4 : ℝ) ^ s = (16 : ℝ) ^ s * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
      rw [zpow_neg, show (2 * (s : ℤ)) = ((2 * s : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
        show (2 : ℝ) ^ (2 * s) = (4 : ℝ) ^ s by rw [pow_mul]; norm_num,
        show (16 : ℝ) ^ s = (4 : ℝ) ^ s * (4 : ℝ) ^ s by rw [← mul_pow]; norm_num]
      field_simp
    dsimp [C]
    rw [h4s_eq]
    field_simp [hX_rpos.ne', hP_pos.ne']
  rw [hfactor]
  rw [show (δ₀ / 4) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) =
      (δ₀ / 4) * ((X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ)))) by ring]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

private lemma bad2_step {X r s Y H : ℕ} {P : Finset ℕ} {ε' W δ₀ η : ℝ}
    (hX_pos : 0 < X)
    (hr_ge : 10 ≤ r) (hr_big : 100 / δ₀ ≤ (r : ℝ))
    (hs_ge9 : 9 ≤ s) (hs_r : s + 1 = r)
    (hH : H = r ^ 7)
    (hY_ge1 : 1 ≤ Y)
    (hY_le_2pow : (Y : ℝ) ≤ 2 * (2 * (X : ℝ)) ^ (1 / (r : ℝ)))
    (hY_ge_2Xr : (2 * (X : ℝ)) ^ (1 / (r : ℝ)) ≤ Y)
    (h2Y_le_exp_α3 : 2 * (Y : ℝ) ≤ Real.exp (Real.log (X : ℝ) ^ (1 / 2 + ε' / 2)))
    (hW_def : W = (2 * (H : ℝ) + 1) ^ (5 * r) * (2048 : ℝ) ^ r)
    (hW_ratio_Y : W * (1000 / δ₀) ≤ Y)
    (hX_ge_W : W * (1000 / δ₀) ≤ X)
    (hP_sub : P ⊆ Finset.Ioc Y (2 * Y))
    (hP_prime : ∀ p ∈ P, p.Prime)
    (hP_ge_W : W * (1000 / δ₀) ≤ P.card)
    (hδ₀_pos : 0 < δ₀) (hδ₀_ub : δ₀ ≤ 1 / 8) (h3δ₀_lt : 3 * δ₀ < η) :
    ((bad2Finset X ε').card : ℝ) / (X : ℝ) < η := by
  have hX_rpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hW_pos : 0 < W := by rw [hW_def]; positivity
  have hP_pos : (0 : ℝ) < P.card := lt_of_lt_of_le (by positivity) hP_ge_W
  have hH_ge1 : 1 ≤ H := by rw [hH]; exact Nat.one_le_pow 7 r (by omega)
  have h2H1_ge2 : 2 ≤ 2 * H + 1 := by omega
  have hW_ge_2s2H : 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (s + 1) ≤ W := by
    have hs_r_le : (s : ℝ) ≤ r := by exact_mod_cast (by omega : s ≤ r)
    have hs2_r2 : (s : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hs_r_le 2
    have hr2_H : (r : ℝ) ^ 2 ≤ H := by
      have : r ^ 2 ≤ r ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
      rw [← hH] at this
      exact_mod_cast this
    have hs2_H : (s : ℝ) ^ 2 ≤ H := hs2_r2.trans hr2_H
    have h1 : (2 * (s : ℝ) ^ 2 * H) ≤ (2 * (H : ℝ) + 1) ^ 2 := by
      have hsq : 2 * (s : ℝ) ^ 2 * H ≤ 2 * (H : ℝ) ^ 2 := by
        calc 2 * (s : ℝ) ^ 2 * H ≤ 2 * (H : ℝ) * H :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs2_H (by norm_num)) (by positivity)
          _ = 2 * (H : ℝ) ^ 2 := by ring
      have hsq_nn : (0 : ℝ) ≤ (H : ℝ) ^ 2 := by positivity
      have hH_nn : (0 : ℝ) ≤ H := by positivity
      linarith [show (2 * (H : ℝ) + 1) ^ 2 = 4 * (H : ℝ) ^ 2 + 4 * (H : ℝ) + 1 by ring]
    have h2 : (2 * (H : ℝ) + 1) ^ 2 ≤ (2 * (H : ℝ) + 1) ^ (5 * r) :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ 2 * H + 1)) (by omega)
    have h3 : (2 : ℝ) ^ (s + 1) ≤ (2048 : ℝ) ^ r := by
      rw [hs_r]; exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
    rw [hW_def]
    exact mul_le_mul (h1.trans h2) h3 (by positivity) (by positivity)
  have hW_le_Y : W ≤ Y := by
    have h1 : 1 ≤ 1000 / δ₀ := (le_div_iff₀ hδ₀_pos).mpr (by linarith)
    calc W = W * 1 := (mul_one W).symm
      _ ≤ W * (1000 / δ₀) := mul_le_mul_of_nonneg_left h1 hW_pos.le
      _ ≤ Y := hW_ratio_Y
  have hdom : 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (s + 1) ≤ Y := hW_ge_2s2H.trans hW_le_Y
  have hfreq_ub : (s : ℝ) * H / Y ≤ 1 / 8 := by
    have hs9 : (9 : ℝ) ≤ s := by exact_mod_cast hs_ge9
    have h2pow : (1024 : ℝ) ≤ (2 : ℝ) ^ (s + 1) := by
      calc (1024 : ℝ) = (2 : ℝ) ^ 10 := by norm_num
        _ ≤ (2 : ℝ) ^ (s + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hY_pos' : (0 : ℝ) < Y := by exact_mod_cast hY_ge1
    rw [div_le_iff₀ hY_pos']
    have hsH_nn : 0 ≤ (s : ℝ) * H := by positivity
    have h2s : 8 * ((s : ℝ) * H) ≤ 2 * (s : ℝ) * ((s : ℝ) * H) * 1024 := by
      have h18 : (18 : ℝ) ≤ 2 * (s : ℝ) := by linarith
      calc 8 * ((s : ℝ) * H) ≤ 18 * ((s : ℝ) * H) * 1024 := by linarith
        _ ≤ 2 * (s : ℝ) * ((s : ℝ) * H) * 1024 := by gcongr
    have hs_prod : 8 * ((s : ℝ) * H) ≤ 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (s + 1) := by
      calc 8 * ((s : ℝ) * H) ≤ 2 * (s : ℝ) * ((s : ℝ) * H) * 1024 := h2s
        _ = 2 * (s : ℝ) ^ 2 * H * 1024 := by ring
        _ ≤ 2 * (s : ℝ) ^ 2 * H * (2 : ℝ) ^ (s + 1) :=
            mul_le_mul_of_nonneg_left h2pow (by positivity)
    linarith [hs_prod, hdom]
  have hW_ge_4r : 4 * (4 : ℝ) ^ r ≤ W := by
    have h1 : (4 : ℝ) ≤ (2 * (H : ℝ) + 1) ^ (5 * r) := by
      calc (4 : ℝ) ≤ (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ (5 * r) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ (2 * (H : ℝ) + 1) ^ (5 * r) :=
          pow_le_pow_left₀ (by norm_num) (by exact_mod_cast h2H1_ge2) (5 * r)
    have h2 : (4 : ℝ) ^ r ≤ (2048 : ℝ) ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
    rw [hW_def]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  let δ : ℝ := 1 / (r : ℝ) ^ 2
  have hδ_pos : 0 < δ := by positivity
  have hδ_le : δ ≤ 1 / 8 := by
    dsimp [δ]; refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) ?_
    have h10 : (10 : ℝ) ≤ r := by exact_mod_cast hr_ge
    calc (8 : ℝ) ≤ 10 * 10 := by norm_num
      _ ≤ (r : ℝ) * (r : ℝ) := mul_le_mul h10 h10 (by positivity) (by positivity)
      _ = (r : ℝ) ^ 2 := by ring
  have hη_F_half : 1 / (4 * ((H : ℝ) + 1) * δ ^ 2) ≤ 1 / 2 := by
    have hden : 4 * (r : ℝ) ^ 3 ≤ 4 * ((H : ℝ) + 1) * δ ^ 2 := by
      dsimp [δ]; rw [hH]; push_cast
      rw [show 4 * ((r : ℝ) ^ 7 + 1) * (1 / (r : ℝ) ^ 2) ^ 2 = 4 * (r : ℝ) ^ 3 + 4 / (r : ℝ) ^ 4 by
        field_simp]
      linarith [show (0 : ℝ) ≤ 4 / (r : ℝ) ^ 4 by positivity]
    have h1 : 1 / (4 * ((H : ℝ) + 1) * δ ^ 2) ≤ 1 / (4 * (r : ℝ) ^ 3) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    refine h1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h10 : (10 : ℝ) ≤ r := by exact_mod_cast hr_ge
    have hr3 : (1 : ℝ) ≤ (r : ℝ) ^ 3 := one_le_pow₀ (by linarith)
    linarith
  obtain ⟨c, T, hT_sum, hT_nn, hT_ge1, hc_zero_eq, hc_bound⟩ :=
    fejerMajorant_exists H δ hδ_pos hδ_le hη_F_half
  let c0 : ℝ := (1 / 2 + 2 * δ) / (1 - 1 / (4 * ((H : ℝ) + 1) * δ ^ 2))
  have hc0_nn : 0 ≤ c0 := by
    have : 0 < 1 - 1 / (4 * ((H : ℝ) + 1) * δ ^ 2) := by linarith
    dsimp [c0]; positivity
  have hc0_pow_le : c0 ^ (2 * s) ≤ (1 + δ₀ / 2) * (2 : ℝ) ^ (-(2 * (s : ℤ))) :=
    bad2_c0_pow_le hr_ge (by omega : s ≤ r) hH hδ₀_pos hδ₀_ub hr_big
  have hp_pow_ratio : ∀ p ∈ P, (p : ℝ) ^ s / (X : ℝ) ≤ δ₀ :=
    bad2_hp_pow_ratio hX_pos hs_r hY_le_2pow hW_ge_4r hW_ratio_Y hP_sub hW_pos hδ₀_pos
  let Z : ℕ → ℝ := fun n => ∑ p ∈ P, if smallDigits p s n then (1 : ℝ) else 0
  have hC_lb : ∀ p ∈ P,
      (1 - δ₀) * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) ≤
        (((Finset.range X).filter (smallDigits p s)).card : ℝ) :=
    bad2_C_lb hX_pos hP_sub hδ₀_ub hp_pow_ratio
  have hC_ub : ∀ p ∈ P,
      (((Finset.range X).filter (smallDigits p s)).card : ℝ) ≤
        6 * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) :=
    bad2_C_ub hX_pos hs_r hW_def hW_le_Y hP_sub hδ₀_ub hp_pow_ratio
  have hZ_sum_eq : ∑ n ∈ Finset.range X, Z n =
      ∑ p ∈ P, (((Finset.range X).filter (smallDigits p s)).card : ℝ) := by
    dsimp [Z]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Finset.sum_boole]
  have hM1 : (1 - δ₀) * (X : ℝ) * (P.card : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) ≤ ∑ n ∈ Finset.range X, Z n := by
    rw [hZ_sum_eq]
    calc (1 - δ₀) * (X : ℝ) * (P.card : ℝ) * (2 : ℝ) ^ (-(s : ℤ))
        = ∑ _p ∈ P, (1 - δ₀) * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) := by simp; ring
      _ ≤ ∑ p ∈ P, (((Finset.range X).filter (smallDigits p s)).card : ℝ) := Finset.sum_le_sum hC_lb
  have hdiag_le : ∑ n ∈ Finset.range X, Z n ≤
      (δ₀ / 4) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
    have h24_le : 24 * (2 : ℝ) ^ s ≤ δ₀ * (P.card : ℝ) := by
      have h1 : 24 * (2 : ℝ) ^ s ≤ W := by
        rw [hW_def]
        have ha : (24 : ℝ) ≤ (2 * (H : ℝ) + 1) ^ (5 * r) := by
          calc (24 : ℝ) ≤ (2 : ℝ) ^ 5 := by norm_num
            _ ≤ (2 : ℝ) ^ (5 * r) := pow_le_pow_right₀ (by norm_num) (by omega)
            _ ≤ (2 * (H : ℝ) + 1) ^ (5 * r) :=
              pow_le_pow_left₀ (by norm_num) (by exact_mod_cast h2H1_ge2) (5 * r)
        have hb : (2 : ℝ) ^ s ≤ (2048 : ℝ) ^ r := by
          calc (2 : ℝ) ^ s ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) (by omega)
            _ ≤ (2048 : ℝ) ^ r := pow_le_pow_left₀ (by norm_num) (by norm_num) r
        exact mul_le_mul ha hb (by positivity) (by positivity)
      have h2 : W * 1000 ≤ δ₀ * (P.card : ℝ) := by
        have := mul_le_mul_of_nonneg_left hP_ge_W hδ₀_pos.le
        rw [show δ₀ * (W * (1000 / δ₀)) = W * 1000 by field_simp] at this
        exact this
      linarith
    have hZ_ub : ∑ n ∈ Finset.range X, Z n ≤ 6 * (P.card : ℝ) * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) := by
      rw [hZ_sum_eq]
      calc ∑ p ∈ P, (((Finset.range X).filter (smallDigits p s)).card : ℝ)
          ≤ ∑ _p ∈ P, 6 * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) := Finset.sum_le_sum hC_ub
        _ = 6 * (P.card : ℝ) * (X : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) := by simp; ring
    refine hZ_ub.trans ?_
    have h2eq : (2 : ℝ) ^ (-(s : ℤ)) = (2 : ℝ) ^ s * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]; congr 1; omega
    rw [h2eq]
    calc 6 * (P.card : ℝ) * (X : ℝ) * ((2 : ℝ) ^ s * (2 : ℝ) ^ (-(2 * (s : ℤ))))
        = ((24 * (2 : ℝ) ^ s) / 4) * (X : ℝ) * (P.card : ℝ) * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by ring
      _ ≤ ((δ₀ * (P.card : ℝ)) / 4) * (X : ℝ) * (P.card : ℝ) * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by gcongr
      _ = (δ₀ / 4) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by ring
  let B : ℝ := ((2 * (H : ℝ) + 1) ^ (3 * r)) * (16 : ℝ) ^ r
  have hB_pos : 0 < B := by positivity
  have hoff := offdiag_second_moment_le (s := s) (H := H) (Y := Y) (X := X) (P := P)
    (by omega) hY_ge1 hX_pos hP_sub hdom hfreq_ub c T c0 B hB_pos hc0_nn hT_sum hT_nn hT_ge1 hc_zero_eq hc_bound
  have hoff_main_le : (P.card : ℝ) ^ 2 * (X : ℝ) * c0 ^ (2 * s) ≤
      (1 + δ₀ / 2) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
    calc (P.card : ℝ) ^ 2 * (X : ℝ) * c0 ^ (2 * s)
        ≤ (P.card : ℝ) ^ 2 * (X : ℝ) * ((1 + δ₀ / 2) * (2 : ℝ) ^ (-(2 * (s : ℤ)))) :=
          mul_le_mul_of_nonneg_left hc0_pow_le (by positivity)
      _ = (1 + δ₀ / 2) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by ring
  have hoff_err_le :
      ((2 * (H : ℝ) + 1) ^ (2 * s)) * (4 : ℝ) ^ s * (P.card : ℝ) *
        (4 * (P.card : ℝ) + (4 * (B / X) * (2 * (Y : ℝ)) ^ (s + 1) + 1) * X + (P.card : ℝ) * X / (2 * B)) ≤
      (δ₀ / 4) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) :=
    bad2_hoff_err_le hX_pos hr_ge hr_big hs_r hH hY_le_2pow hW_def hX_ge_W hP_ge_W hδ₀_pos
  have hM2 : ∑ n ∈ Finset.range X, Z n ^ 2 ≤
      (1 + δ₀) * (X : ℝ) * (P.card : ℝ) ^ 2 * (2 : ℝ) ^ (-(2 * (s : ℤ))) := by
    have hsq_split : ∑ n ∈ Finset.range X, Z n ^ 2 =
        (∑ n ∈ Finset.range X, Z n) +
          ∑ p ∈ P, ∑ q ∈ P.erase p, ∑ n ∈ Finset.range X,
            (if smallDigits p s n then (1 : ℝ) else 0) * (if smallDigits q s n then (1 : ℝ) else 0) := by
      have hZ_sq : ∀ n : ℕ, Z n ^ 2 =
          Z n + ∑ p ∈ P, ∑ q ∈ P.erase p,
            (if smallDigits p s n then (1 : ℝ) else 0) * (if smallDigits q s n then (1 : ℝ) else 0) := by
        intro n
        dsimp [Z]
        rw [sq, Finset.sum_mul_sum]
        have hinner : ∀ p ∈ P,
            (∑ q ∈ P, (if smallDigits p s n then (1 : ℝ) else 0) * (if smallDigits q s n then (1 : ℝ) else 0)) =
            (if smallDigits p s n then (1 : ℝ) else 0) +
              ∑ q ∈ P.erase p, (if smallDigits p s n then (1 : ℝ) else 0) * (if smallDigits q s n then (1 : ℝ) else 0) := by
          intro p hp
          rw [← Finset.add_sum_erase P _ hp]
          congr 1
          split_ifs <;> ring
        rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
      simp_rw [hZ_sq, Finset.sum_add_distrib]
      congr 1
      simp_rw [Finset.sum_comm (s := Finset.range X)]
    rw [hsq_split]
    have htot_off := hoff.trans (add_le_add hoff_main_le hoff_err_le)
    linarith
  let Good := (Finset.range X).filter (fun n => ∃ p ∈ P, smallDigits p s n)
  let Bad := bad2Finset X ε'
  have hGood_sub : Good ⊆ Finset.range X := Finset.filter_subset _ _
  have hBad_sub : Bad ⊆ Finset.range X := fun n hn =>
    Finset.mem_range.mpr (mem_bad2Finset.mp hn).1
  have hDisj : Disjoint Good Bad := by
    rw [Finset.disjoint_left]
    intro n hnGood hnBad
    rw [Finset.mem_filter, Finset.mem_range] at hnGood
    have hnBad' := (mem_bad2Finset.mp hnBad).2
    rcases hnGood.2 with ⟨p, hpP, hsd⟩
    have hp_mem := Finset.mem_Ioc.mp (hP_sub hpP)
    have hp_prime := hP_prime p hpP
    have hp_le_exp : (p : ℝ) ≤ Real.exp (Real.log (X : ℝ) ^ (1 / 2 + ε' / 2)) :=
      (show (p : ℝ) ≤ 2 * Y by exact_mod_cast hp_mem.2).trans h2Y_le_exp_α3
    have h2n_lt_pr : 2 * n < p ^ r := by
      have hY_lt_p : (Y : ℝ) < p := by exact_mod_cast hp_mem.1
      have h2X_lt_pr : 2 * (X : ℝ) < (p : ℝ) ^ r := by
        have h2X_eq : (((2 * (X : ℝ)) ^ (1 / (r : ℝ))) ^ r) = 2 * (X : ℝ) := by
          rw [← Real.rpow_natCast ((2 * (X : ℝ)) ^ (1 / (r : ℝ))) r, ← Real.rpow_mul (by positivity)]
          simp [hr_pos.ne']
        rw [← h2X_eq]
        exact pow_lt_pow_left₀ (lt_of_le_of_lt hY_ge_2Xr hY_lt_p) (by positivity) (by omega)
      have h2X_nat : 2 * X < p ^ r := by exact_mod_cast h2X_lt_pr
      omega
    have hsd_r1 : ∀ j ∈ Finset.range (r - 1), 2 * basePDigit p n j < p := fun j hj =>
      hsd j (Finset.mem_range.mpr (by rw [Finset.mem_range] at hj; omega))
    have hndvd := not_dvd_centralBinom_of_small_digits hp_prime h2n_lt_pr hsd_r1
    exact hndvd (hnBad' p hp_prime hp_le_exp)
  have hZ_zero : ∀ n ∈ Finset.range X, n ∉ Good → Z n = 0 := by
    intro n hn hnot
    have hno : ∀ p ∈ P, ¬ smallDigits p s n := by
      intro p hp hsd
      exact hnot (Finset.mem_filter.mpr ⟨hn, p, hp, hsd⟩)
    dsimp [Z]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg (hno p hp)]
  exact bad2_moment_finish hX_pos hP_pos hδ₀_pos hδ₀_ub h3δ₀_lt hGood_sub hBad_sub hDisj Z hZ_zero hM1 hM2

private lemma bad2_density_tendsto_zero (ε' : ℝ) (hε' : 0 < ε') (hε'1 : ε' ≤ 1 / 4) :
    Tendsto (fun X : ℕ => ((bad2Finset X ε').card : ℝ) / X) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  let δ₀ : ℝ := min (η / 8) (1 / 8)
  have hδ₀_pos : 0 < δ₀ := lt_min (by linarith) (by norm_num)
  have hδ₀_ub : δ₀ ≤ 1 / 8 := min_le_right _ _
  have h3δ₀_lt : 3 * δ₀ < η := by
    have h : δ₀ ≤ η / 8 := min_le_left _ _
    linarith
  let α₁ : ℝ := 1 / 2 - ε' / 4
  let α₂ : ℝ := 1 / 2 + ε' / 4
  let α₃ : ℝ := 1 / 2 + ε' / 2
  have hα₁_pos : 0 < α₁ := by dsimp [α₁]; linarith
  have hα₂_pos : 0 < α₂ := by dsimp [α₂]; linarith
  have hlog_top : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have heps38_top : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ (3 * ε' / 8)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 3 * ε' / 8)).comp hlog_top
  have heps4_top : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ (ε' / 4)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < ε' / 4)).comp hlog_top
  have hα₁_top : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ α₁) atTop atTop :=
    (tendsto_rpow_atTop hα₁_pos).comp hlog_top
  have hα₂_top : Tendsto (fun X : ℕ => Real.log (X : ℝ) ^ α₂) atTop atTop :=
    (tendsto_rpow_atTop hα₂_pos).comp hlog_top
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp card_primes_Ioc_ge
  let K0 : ℝ := 16 * (1 + 8 / ε') + Real.log 2048
  let M6 : ℝ := 8 * max 1 (Real.log (1000 / δ₀ + (Y₀ : ℝ)))
  have hev1 : ∀ᶠ X : ℕ in atTop, 100 ≤ Real.log (X : ℝ) := hlog_top.eventually_ge_atTop 100
  have hev2 : ∀ᶠ X : ℕ in atTop, max 10 (100 / δ₀) ≤ Real.log (X : ℝ) ^ α₁ :=
    hα₁_top.eventually_ge_atTop (max 10 (100 / δ₀))
  have hev3 : ∀ᶠ X : ℕ in atTop, max (max (Y₀ : ℝ) 10000) M6 ≤ Real.log (X : ℝ) ^ α₂ :=
    hα₂_top.eventually_ge_atTop (max (max (Y₀ : ℝ) 10000) M6)
  have hev4 : ∀ᶠ X : ℕ in atTop, 20 * K0 + 100 ≤ Real.log (X : ℝ) ^ (3 * ε' / 8) :=
    heps38_top.eventually_ge_atTop (20 * K0 + 100)
  have hev5 : ∀ᶠ X : ℕ in atTop, 10 ≤ Real.log (X : ℝ) ^ (ε' / 4) :=
    heps4_top.eventually_ge_atTop 10
  have h_final : ∀ᶠ X : ℕ in atTop, ((bad2Finset X ε').card : ℝ) / X < η := by
    have hev_all := hev1.and (hev2.and (hev3.and (hev4.and hev5)))
    filter_upwards [hev_all] with X ⟨hlog100, hLα1, hLα2, h38, h14⟩
    have hX_pos : 0 < X := by
      by_contra h0
      have hX0 : X = 0 := by omega
      subst hX0
      simp at hlog100
      linarith
    have hX_rpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
    let L : ℝ := Real.log (X : ℝ)
    have hL_pos : 0 < L := by linarith
    have hLα1_10 : 10 ≤ L ^ α₁ := le_trans (le_max_left _ _) hLα1
    have hLα1_δ : 100 / δ₀ ≤ L ^ α₁ := le_trans (le_max_right _ _) hLα1
    have hLα2_10000 : 10000 ≤ L ^ α₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLα2
    have hLα2_Y0 : (Y₀ : ℝ) ≤ L ^ α₂ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLα2
    have hexp_big : 1000 / δ₀ + (Y₀ : ℝ) ≤ Real.exp ((1 / 8) * L ^ α₂) := by
      have hM6_le : M6 ≤ L ^ α₂ := le_trans (le_max_right _ _) hLα2
      have hlog_le : Real.log (1000 / δ₀ + (Y₀ : ℝ)) ≤ (1 / 8) * L ^ α₂ := by
        have : Real.log (1000 / δ₀ + (Y₀ : ℝ)) ≤ M6 / 8 := by
          dsimp [M6]; linarith [le_max_right 1 (Real.log (1000 / δ₀ + (Y₀ : ℝ)))]
        linarith
      calc 1000 / δ₀ + (Y₀ : ℝ)
          = Real.exp (Real.log (1000 / δ₀ + (Y₀ : ℝ))) := (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp ((1 / 8) * L ^ α₂) := Real.exp_le_exp.mpr hlog_le
    let r : ℕ := Nat.ceil (L ^ α₁)
    have hr_ge : 10 ≤ r := by
      have : (10 : ℝ) ≤ r := hLα1_10.trans (Nat.le_ceil _)
      exact_mod_cast this
    have hr_big : 100 / δ₀ ≤ (r : ℝ) := hLα1_δ.trans (Nat.le_ceil _)
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have hr_ub : (r : ℝ) ≤ 2 * L ^ α₁ := by
      have h1 : (r : ℝ) < L ^ α₁ + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    let s : ℕ := r - 1
    have hs_ge9 : 9 ≤ s := by dsimp [s]; omega
    have hs_r : s + 1 = r := by dsimp [s]; omega
    let Y : ℕ := Nat.ceil ((2 * (X : ℝ)) ^ (1 / (r : ℝ)))
    have h2X_eq_exp : (2 * (X : ℝ)) ^ (1 / (r : ℝ)) = Real.exp (Real.log (2 * (X : ℝ)) / r) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      ring_nf
    have hlog2X_ge : L ≤ Real.log (2 * (X : ℝ)) := Real.log_le_log hX_rpos (by linarith)
    have hlog2X_le : Real.log (2 * (X : ℝ)) ≤ 2 * L := by
      rw [Real.log_mul (by norm_num) hX_rpos.ne']
      have : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hL_rpow_id : L / L ^ α₁ = L ^ α₂ := by
      calc L / L ^ α₁ = L ^ (1 : ℝ) / L ^ α₁ := by rw [Real.rpow_one]
        _ = L ^ ((1 : ℝ) - α₁) := (Real.rpow_sub hL_pos _ _).symm
        _ = L ^ α₂ := by congr 1; dsimp [α₁, α₂]; ring
    have hY_ge_exp : Real.exp ((1 / 2) * L ^ α₂) ≤ Y := by
      have hdiv_ge : (1 / 2) * L ^ α₂ ≤ Real.log (2 * (X : ℝ)) / r := by
        calc (1 / 2) * L ^ α₂
            = L / (2 * L ^ α₁) := by rw [← hL_rpow_id]; ring
          _ ≤ Real.log (2 * (X : ℝ)) / r := div_le_div₀ (by linarith) hlog2X_ge hr_pos hr_ub
      calc Real.exp ((1 / 2) * L ^ α₂)
          ≤ Real.exp (Real.log (2 * (X : ℝ)) / r) := Real.exp_le_exp.mpr hdiv_ge
        _ = (2 * (X : ℝ)) ^ (1 / (r : ℝ)) := h2X_eq_exp.symm
        _ ≤ Y := Nat.le_ceil _
    have hY_le_2pow : (Y : ℝ) ≤ 2 * (2 * (X : ℝ)) ^ (1 / (r : ℝ)) := by
      have hceil_lt : (Y : ℝ) < (2 * (X : ℝ)) ^ (1 / (r : ℝ)) + 1 := Nat.ceil_lt_add_one (by positivity)
      have hpow_ge1 : 1 ≤ (2 * (X : ℝ)) ^ (1 / (r : ℝ)) := by
        rw [h2X_eq_exp, Real.one_le_exp_iff]
        exact div_nonneg (by linarith) hr_pos.le
      linarith
    have hY_le_exp : (Y : ℝ) ≤ 2 * Real.exp (2 * L ^ α₂) := by
      have hdiv_le : Real.log (2 * (X : ℝ)) / r ≤ 2 * L ^ α₂ := by
        calc Real.log (2 * (X : ℝ)) / r
            ≤ (2 * L) / (L ^ α₁) := div_le_div₀ (by positivity) hlog2X_le (by positivity) (Nat.le_ceil _)
          _ = 2 * L ^ α₂ := by rw [← hL_rpow_id]; ring
      have hexp_le : (2 * (X : ℝ)) ^ (1 / (r : ℝ)) ≤ Real.exp (2 * L ^ α₂) := by
        rw [h2X_eq_exp]; exact Real.exp_le_exp.mpr hdiv_le
      linarith
    have h2Y_le_exp_α3 : 2 * (Y : ℝ) ≤ Real.exp (L ^ α₃) := by
      have hlog4 : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith [Real.log_two_lt_d9]
      have hα3_eq : L ^ α₃ = L ^ α₂ * L ^ (ε' / 4) := by
        rw [← Real.rpow_add hL_pos]
        congr 1; dsimp [α₂, α₃]; ring
      have hmul_ge : L ^ α₂ * 10 ≤ L ^ α₂ * L ^ (ε' / 4) :=
        mul_le_mul_of_nonneg_left h14 (by positivity)
      have hsum_le : Real.log 4 + 2 * L ^ α₂ ≤ L ^ α₃ := by rw [hα3_eq]; linarith
      calc 2 * (Y : ℝ) ≤ 4 * Real.exp (2 * L ^ α₂) := by linarith
        _ = Real.exp (Real.log 4 + 2 * L ^ α₂) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
        _ ≤ Real.exp (L ^ α₃) := Real.exp_le_exp.mpr hsum_le
    let H : ℕ := r ^ 7
    let W : ℝ := (2 * (H : ℝ) + 1) ^ (5 * r) * (2048 : ℝ) ^ r
    have hW_pos : 0 < W := by positivity
    have hW_le_exp : W ≤ Real.exp ((1 / 4) * L ^ α₂) :=
      bad2_asymp_W_le_exp hε' hlog100 hr_ge rfl hr_ub h38
    have hLα2_nn : 0 ≤ L ^ α₂ := Real.rpow_nonneg hL_pos.le _
    have hW_ratio_Y : W * (1000 / δ₀) ≤ Y := by
      have h1 : Real.exp ((1 / 4) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂) ≤ Real.exp ((1 / 2) * L ^ α₂) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      calc W * (1000 / δ₀)
          ≤ Real.exp ((1 / 4) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂) :=
            mul_le_mul hW_le_exp (by linarith) (by positivity) (by positivity)
        _ ≤ Real.exp ((1 / 2) * L ^ α₂) := h1
        _ ≤ Y := hY_ge_exp
    have hY_ge_Y0 : Y₀ ≤ Y := by
      have h1 : (Y₀ : ℝ) ≤ Real.exp ((1 / 8) * L ^ α₂) := by linarith [show 0 < 1000 / δ₀ by positivity]
      have h2 : Real.exp ((1 / 8) * L ^ α₂) ≤ Real.exp ((1 / 2) * L ^ α₂) :=
        Real.exp_le_exp.mpr (by linarith)
      exact_mod_cast (h1.trans (h2.trans hY_ge_exp))
    have hY_ge1 : 1 ≤ Y := by
      have h3 : (50 : ℝ) ≤ Y := by
        have hexp_ge := Real.add_one_le_exp ((1 / 2) * L ^ α₂)
        calc (50 : ℝ) ≤ (1 / 2) * L ^ α₂ + 1 := by linarith
          _ ≤ Real.exp ((1 / 2) * L ^ α₂) := hexp_ge
          _ ≤ Y := hY_ge_exp
      exact_mod_cast (by linarith : (1 : ℝ) ≤ Y)
    have hY_pos : 0 < Y := hY_ge1
    let P : Finset ℕ := (Finset.Ioc Y (2 * Y)).filter Nat.Prime
    have hP_sub : P ⊆ Finset.Ioc Y (2 * Y) := Finset.filter_subset _ _
    have hP_ge_ratio : (Y : ℝ) / (4 * Real.log (2 * Y)) ≤ P.card := hY₀ Y hY_ge_Y0
    have hlog2Y_ub : 4 * Real.log (2 * (Y : ℝ)) ≤ Real.exp ((1 / 8) * L ^ α₂) :=
      bad2_log2Y_ub hLα2_10000 hY_pos hY_le_exp
    have hP_ge_W : W * (1000 / δ₀) ≤ P.card := by
      have hexp_split : Real.exp ((1 / 4) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂) ≤
          Real.exp ((1 / 2) * L ^ α₂) := by
        rw [← Real.exp_add, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      calc W * (1000 / δ₀)
          ≤ Real.exp ((1 / 4) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂) :=
            mul_le_mul hW_le_exp (by linarith) (by positivity) (by positivity)
        _ = (Real.exp ((1 / 4) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂)) /
              Real.exp ((1 / 8) * L ^ α₂) := by field_simp
        _ ≤ (Y : ℝ) / Real.exp ((1 / 8) * L ^ α₂) :=
            div_le_div_of_nonneg_right (hexp_split.trans hY_ge_exp) (by positivity)
        _ ≤ (Y : ℝ) / (4 * Real.log (2 * Y)) :=
            div_le_div_of_nonneg_left (by positivity)
              (mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * Y))))
              hlog2Y_ub
        _ ≤ P.card := hP_ge_ratio
    have hP_pos : (0 : ℝ) < P.card := by
      have hW_big : 0 < W * (1000 / δ₀) := by positivity
      exact hW_big.trans_le hP_ge_W
    have hX_ge_W : W * (1000 / δ₀) ≤ (X : ℝ) := by
      have hα₂_le : α₂ ≤ 1 := by dsimp [α₂]; linarith
      have hL_ge_half : (1 / 2) * L ^ α₂ ≤ L := by
        have h1 : L ^ α₂ ≤ L := Real.rpow_le_self_of_one_le (by linarith) hα₂_le
        linarith
      have h1 : Real.exp ((1 / 4) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂) ≤ Real.exp L := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      calc W * (1000 / δ₀)
          ≤ Real.exp ((1 / 4) * L ^ α₂) * Real.exp ((1 / 8) * L ^ α₂) :=
            mul_le_mul hW_le_exp (by linarith) (by positivity) (by positivity)
        _ ≤ Real.exp L := h1
        _ = (X : ℝ) := Real.exp_log hX_rpos
    have hP_prime : ∀ p ∈ P, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2
    exact bad2_step hX_pos hr_ge hr_big hs_ge9 hs_r rfl hY_ge1 hY_le_2pow (Nat.le_ceil _)
      h2Y_le_exp_α3 rfl hW_ratio_Y hX_ge_W hP_sub hP_prime hP_ge_W hδ₀_pos hδ₀_ub h3δ₀_lt
  exact h_final.mono fun X hX => by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    exact hX

private theorem erdos_731_egrs75_proof : ∀ ε > (0 : ℝ),
    {n : ℕ | Real.exp (Real.log n ^ ((1 : ℝ) / 2 - ε)) < (Erdos731.leastNonDivisor n : ℝ) ∧
      (Erdos731.leastNonDivisor n : ℝ) < Real.exp (Real.log n ^ ((1 : ℝ) / 2 + ε))}.HasDensity 1 := by
  intro ε hε
  let ε' : ℝ := min ε (1 / 4)
  have hε'_pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'_le1 : ε' ≤ 1 / 4 := min_le_right _ _
  have hε'_le : ε' ≤ ε := min_le_left _ _
  let S : Set ℕ := {n : ℕ |
    Real.exp (Real.log n ^ ((1 : ℝ) / 2 - ε)) < (Erdos731.leastNonDivisor n : ℝ) ∧
      (Erdos731.leastNonDivisor n : ℝ) < Real.exp (Real.log n ^ ((1 : ℝ) / 2 + ε))}
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter, Set.ncard_Iio_nat]
  rw [Metric.tendsto_nhds]
  intro η hη
  let δ₁ : ℝ := min (η / 4) (1 / 4)
  have hδ₁_pos : 0 < δ₁ := lt_min (by linarith) (by norm_num)
  have hδ₁_le_eta : δ₁ ≤ η / 4 := min_le_left _ _
  have hδ₁_le_q : δ₁ ≤ 1 / 4 := min_le_right _ _
  have hb1 : ∀ᶠ X : ℕ in atTop,
      (((Finset.range X).filter (fun n =>
        ∃ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (Real.log X ^ (1 / 2 - ε' / 2)))),
          ¬ m ∣ n.centralBinom)).card : ℝ) / X < η / 4 :=
    (Metric.tendsto_nhds.mp (bad1_density_tendsto_zero ε' hε'_pos hε'_le1) (η / 4) (by positivity)).mono
      fun X hX => by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hX
        exact hX
  have hb2 : ∀ᶠ X : ℕ in atTop,
      ((bad2Finset X ε').card : ℝ) / X < η / 4 :=
    (Metric.tendsto_nhds.mp (bad2_density_tendsto_zero ε' hε'_pos hε'_le1) (η / 4) (by positivity)).mono
      fun X hX => by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hX
        exact hX
  have hlog_top : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff_exp_pos : 0 < ε - ε' / 2 := by linarith
  have hev_log_ratio : ∀ᶠ X : ℕ in atTop,
      (2 : ℝ) ^ (1 / 2 + ε) < Real.log (X : ℝ) ^ (ε - ε' / 2) :=
    ((tendsto_rpow_atTop hdiff_exp_pos).comp hlog_top).eventually_gt_atTop ((2 : ℝ) ^ (1 / 2 + ε))
  have hev_X_big : ∀ᶠ X : ℕ in atTop,
      max (max 100 (4 / δ₁)) (Real.exp (2 * max 1 (Real.log (2 / δ₁)))) ≤ (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hev_one : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (X : ℝ) ^ (1 / 2 - ε' / 2) :=
    ((tendsto_rpow_atTop (by linarith : 0 < 1 / 2 - ε' / 2)).comp hlog_top).eventually_ge_atTop 1
  filter_upwards [hb1, hb2, hev_log_ratio, hev_X_big, hev_one] with X h1 h2 hratio hXbig h1_le
  have h100 : (100 : ℝ) ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXbig
  have h4δ₁ : 4 / δ₁ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXbig
  have hexp_δ₁ : Real.exp (2 * max 1 (Real.log (2 / δ₁))) ≤ X := le_trans (le_max_right _ _) hXbig
  have hX_pos : 0 < X := by exact_mod_cast (by linarith : (0 : ℝ) < X)
  have hX_rpos : (0 : ℝ) < X := Nat.cast_pos.mpr hX_pos
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogX_ge1 : 1 ≤ Real.log (X : ℝ) := by
    have : Real.exp 1 ≤ X := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (X : ℝ) := Real.log_le_log (Real.exp_pos 1) this
  let X₀ : ℕ := Nat.floor (δ₁ * (X : ℝ))
  have hX₀_ge4 : 4 ≤ X₀ := by
    have h4 : (4 : ℝ) ≤ δ₁ * (X : ℝ) := (div_le_iff₀' hδ₁_pos).mp h4δ₁
    exact Nat.le_floor h4
  have hX₀_le_real : (X₀ : ℝ) ≤ δ₁ * (X : ℝ) := Nat.floor_le (by positivity)
  have hX₀_lt_X : X₀ < X := by
    have : (X₀ : ℝ) ≤ (1 / 4) * (X : ℝ) := hX₀_le_real.trans (mul_le_mul_of_nonneg_right hδ₁_le_q hX_rpos.le)
    exact_mod_cast (by linarith : (X₀ : ℝ) < (X : ℝ))
  have hX₀_lb : (δ₁ / 2) * (X : ℝ) ≤ X₀ := by
    have h4 : (4 : ℝ) ≤ δ₁ * (X : ℝ) := (div_le_iff₀' hδ₁_pos).mp h4δ₁
    have hfl := Nat.lt_floor_add_one (δ₁ * (X : ℝ))
    have : δ₁ * (X : ℝ) - 1 ≤ X₀ := by linarith
    linarith
  let Bad1 := (Finset.range X).filter (fun n =>
    ∃ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (Real.log X ^ (1 / 2 - ε' / 2)))), ¬ m ∣ n.centralBinom)
  let Bad2 := bad2Finset X ε'
  let Good := (Finset.Ico X₀ X) \ (Bad1 ∪ Bad2)
  have hGood_sub_range : Good ⊆ Finset.range X := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hn).1).2
  have hGood_in_S : ∀ n ∈ Good, n ∈ S := by
    intro n hn
    have hmem := Finset.mem_sdiff.mp hn
    have hIco := Finset.mem_Ico.mp hmem.1
    have hnot1 : n ∉ Bad1 := fun h => hmem.2 (Finset.mem_union_left _ h)
    have hnot2 : n ∉ Bad2 := fun h => hmem.2 (Finset.mem_union_right _ h)
    have hn_lt : n < X := hIco.2
    have hn_ge4 : 4 ≤ n := hX₀_ge4.trans hIco.1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlogn_ge1 : 1 ≤ Real.log (n : ℝ) := by
      have h3 : Real.exp 1 ≤ n := by
        have : (4 : ℝ) ≤ n := by exact_mod_cast hn_ge4
        linarith [Real.exp_one_lt_d9]
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 1) h3
    have hlogn_le_X : Real.log (n : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hn_pos (by exact_mod_cast hn_lt.le)
    have hlogn_ge_half : (1 / 2) * Real.log (X : ℝ) ≤ Real.log (n : ℝ) := by
      have hn_r_ge : (δ₁ / 2) * (X : ℝ) ≤ n := hX₀_lb.trans (by exact_mod_cast hIco.1)
      have hlog_eq : Real.log ((δ₁ / 2) * (X : ℝ)) = Real.log (X : ℝ) - Real.log (2 / δ₁) := by
        rw [Real.log_mul (by positivity) hX_rpos.ne', show δ₁ / 2 = (2 / δ₁)⁻¹ by field_simp,
          Real.log_inv]
        ring
      have hlog2_le : Real.log (2 / δ₁) ≤ (1 / 2) * Real.log (X : ℝ) := by
        have h1 : Real.log (2 / δ₁) ≤ max 1 (Real.log (2 / δ₁)) := le_max_right _ _
        have h2 : 2 * max 1 (Real.log (2 / δ₁)) ≤ Real.log (X : ℝ) := by
          calc 2 * max 1 (Real.log (2 / δ₁))
              = Real.log (Real.exp (2 * max 1 (Real.log (2 / δ₁)))) := (Real.log_exp _).symm
            _ ≤ Real.log (X : ℝ) := Real.log_le_log (Real.exp_pos _) hexp_δ₁
        linarith
      calc (1 / 2) * Real.log (X : ℝ)
          ≤ Real.log (X : ℝ) - Real.log (2 / δ₁) := by linarith
        _ = Real.log ((δ₁ / 2) * (X : ℝ)) := hlog_eq.symm
        _ ≤ Real.log (n : ℝ) := Real.log_le_log (by positivity) hn_r_ge
    have hne_set : {m : ℕ | 0 < m ∧ ¬ m ∣ Nat.centralBinom n}.Nonempty := by
      refine ⟨Nat.centralBinom n + 1, Nat.succ_pos _, ?_⟩
      intro hdvd
      have hle := Nat.le_of_dvd (Nat.centralBinom_pos n) hdvd
      omega
    have hinf_mem := Nat.sInf_mem hne_set
    have hlb : Real.exp (Real.log (n : ℝ) ^ ((1 : ℝ) / 2 - ε)) < (Erdos731.leastNonDivisor n : ℝ) := by
      have hall_dvd : ∀ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (Real.log X ^ (1 / 2 - ε' / 2)))),
          m ∣ Nat.centralBinom n := by
        intro m hm
        by_contra hndvd
        exact hnot1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn_lt, m, hm, hndvd⟩)
      have hgt_floor : Nat.floor (Real.exp (Real.log X ^ (1 / 2 - ε' / 2))) < Erdos731.leastNonDivisor n := by
        by_contra hle
        have hmem_Icc : Erdos731.leastNonDivisor n ∈ Finset.Icc 1 (Nat.floor (Real.exp (Real.log X ^ (1 / 2 - ε' / 2)))) :=
          Finset.mem_Icc.mpr ⟨hinf_mem.1, by omega⟩
        exact hinf_mem.2 (hall_dvd _ hmem_Icc)
      have hexp_lt_lnd : Real.exp (Real.log (X : ℝ) ^ (1 / 2 - ε' / 2)) < (Erdos731.leastNonDivisor n : ℝ) := by
        have h1 : Real.exp (Real.log (X : ℝ) ^ (1 / 2 - ε' / 2)) <
            (Nat.floor (Real.exp (Real.log (X : ℝ) ^ (1 / 2 - ε' / 2))) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have h2 : (Nat.floor (Real.exp (Real.log (X : ℝ) ^ (1 / 2 - ε' / 2))) : ℝ) + 1 ≤
            (Erdos731.leastNonDivisor n : ℝ) := by exact_mod_cast hgt_floor
        exact h1.trans_le h2
      have hpow_le : Real.log (n : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ Real.log (X : ℝ) ^ (1 / 2 - ε' / 2) := by
        rcases le_or_gt ((1 : ℝ) / 2 - ε) 0 with hneg | hpos
        · exact (Real.rpow_le_one_of_one_le_of_nonpos hlogn_ge1 hneg).trans h1_le
        · calc Real.log (n : ℝ) ^ ((1 : ℝ) / 2 - ε)
              ≤ Real.log (X : ℝ) ^ ((1 : ℝ) / 2 - ε) :=
                Real.rpow_le_rpow (by linarith) hlogn_le_X hpos.le
            _ ≤ Real.log (X : ℝ) ^ (1 / 2 - ε' / 2) :=
                Real.rpow_le_rpow_of_exponent_le hlogX_ge1 (by linarith)
      exact (Real.exp_le_exp.mpr hpow_le).trans_lt hexp_lt_lnd
    have hub : (Erdos731.leastNonDivisor n : ℝ) < Real.exp (Real.log (n : ℝ) ^ ((1 : ℝ) / 2 + ε)) := by
      have hex_p : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ Real.exp (Real.log X ^ (1 / 2 + ε' / 2)) ∧
          ¬ p ∣ Nat.centralBinom n := by
        by_contra hnone
        push Not at hnone
        exact hnot2 (mem_bad2Finset.mpr ⟨hn_lt, hnone⟩)
      rcases hex_p with ⟨p, hp_prime, hp_ub, hp_ndvd⟩
      have hlnd_le_p : Erdos731.leastNonDivisor n ≤ p := Nat.sInf_le ⟨hp_prime.pos, hp_ndvd⟩
      have hlnd_le_exp : (Erdos731.leastNonDivisor n : ℝ) ≤ Real.exp (Real.log (X : ℝ) ^ (1 / 2 + ε' / 2)) :=
        (show (Erdos731.leastNonDivisor n : ℝ) ≤ p by exact_mod_cast hlnd_le_p).trans hp_ub
      have hpow_lt : Real.log (X : ℝ) ^ (1 / 2 + ε' / 2) < Real.log (n : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
        have hmul1 : Real.log (X : ℝ) ^ (1 / 2 + ε' / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2 + ε) <
            Real.log (X : ℝ) ^ (1 / 2 + ε' / 2) * Real.log (X : ℝ) ^ (ε - ε' / 2) :=
          mul_lt_mul_of_pos_left hratio (Real.rpow_pos_of_pos hlogX_pos _)
        have hadd_exp : Real.log (X : ℝ) ^ (1 / 2 + ε' / 2) * Real.log (X : ℝ) ^ (ε - ε' / 2) =
            Real.log (X : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
          rw [← Real.rpow_add hlogX_pos]
          congr 1; ring
        have hlt_half : Real.log (X : ℝ) ^ (1 / 2 + ε' / 2) <
            ((1 / 2 : ℝ) * Real.log (X : ℝ)) ^ ((1 : ℝ) / 2 + ε) := by
          rw [Real.mul_rpow (by positivity) hlogX_pos.le,
            show (1 / 2 : ℝ) ^ ((1 : ℝ) / 2 + ε) = ((2 : ℝ) ^ ((1 : ℝ) / 2 + ε))⁻¹ by
              rw [one_div, Real.inv_rpow (by norm_num)]]
          rw [lt_inv_mul_iff₀ (Real.rpow_pos_of_pos (by norm_num) _)]
          linarith
        have hmono : ((1 / 2 : ℝ) * Real.log (X : ℝ)) ^ ((1 : ℝ) / 2 + ε) ≤
            Real.log (n : ℝ) ^ ((1 : ℝ) / 2 + ε) :=
          Real.rpow_le_rpow (by positivity) hlogn_ge_half (by positivity)
        exact hlt_half.trans_le hmono
      exact hlnd_le_exp.trans_lt (Real.exp_lt_exp.mpr hpow_lt)
    exact ⟨hlb, hub⟩
  have hGood_sub_S : (Good : Set ℕ) ⊆ S ∩ Set.Iio X := by
    intro n hn
    rw [Finset.mem_coe] at hn
    exact ⟨hGood_in_S n hn, Finset.mem_range.mp (hGood_sub_range hn)⟩
  have hncard_le_X : (S ∩ Set.Iio X).ncard ≤ X := by
    have hcoe : (Set.Iio X : Set ℕ) = ↑(Finset.range X) := by ext k; simp
    rw [hcoe]
    have h1 := Set.ncard_le_ncard (Set.inter_subset_right (s := S) (t := ↑(Finset.range X)))
      (Finset.finite_toSet (Finset.range X))
    rwa [Set.ncard_coe_finset, Finset.card_range] at h1
  have hGood_le_ncard : Good.card ≤ (S ∩ Set.Iio X).ncard := by
    rw [← Set.ncard_coe_finset Good]
    exact Set.ncard_le_ncard hGood_sub_S
      ((Set.finite_Iio X).subset (Set.inter_subset_right (s := S) (t := Set.Iio X)))
  have hIco_sub : Finset.Ico X₀ X ⊆ Good ∪ (Bad1 ∪ Bad2) := by
    intro n hn
    by_cases hbad : n ∈ Bad1 ∪ Bad2
    · exact Finset.mem_union_right _ hbad
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hn, hbad⟩)
  have hGood_lb : X - X₀ ≤ Good.card + Bad1.card + Bad2.card := by
    have h1 : (Finset.Ico X₀ X).card ≤ (Good ∪ (Bad1 ∪ Bad2)).card := Finset.card_le_card hIco_sub
    have h2 : (Good ∪ (Bad1 ∪ Bad2)).card ≤ Good.card + (Bad1.card + Bad2.card) :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left (Finset.card_union_le _ _) _)
    rw [Nat.card_Ico] at h1
    omega
  have hncard_lb_r : (X : ℝ) - (X₀ : ℝ) - (Bad1.card : ℝ) - (Bad2.card : ℝ) ≤ ((S ∩ Set.Iio X).ncard : ℝ) := by
    have hnat1 : X - X₀ ≤ (S ∩ Set.Iio X).ncard + Bad1.card + Bad2.card := by omega
    have hr1 : ((X - X₀ : ℕ) : ℝ) ≤ ((S ∩ Set.Iio X).ncard : ℝ) + (Bad1.card : ℝ) + (Bad2.card : ℝ) := by
      exact_mod_cast hnat1
    rw [Nat.cast_sub hX₀_lt_X.le] at hr1
    linarith
  have hratio_le1 : ((S ∩ Set.Iio X).ncard : ℝ) / (X : ℝ) ≤ 1 := by
    rw [div_le_one hX_rpos]
    exact_mod_cast hncard_le_X
  have hratio_ge : 1 - (3 / 4) * η < ((S ∩ Set.Iio X).ncard : ℝ) / (X : ℝ) := by
    have hX₀_ratio : (X₀ : ℝ) / (X : ℝ) ≤ η / 4 := by
      rw [div_le_iff₀ hX_rpos]
      exact hX₀_le_real.trans (mul_le_mul_of_nonneg_right hδ₁_le_eta hX_rpos.le)
    have hdiv_lb : 1 - ((X₀ : ℝ) / (X : ℝ) + (Bad1.card : ℝ) / (X : ℝ) + (Bad2.card : ℝ) / (X : ℝ)) ≤
        ((S ∩ Set.Iio X).ncard : ℝ) / (X : ℝ) := by
      have h1 : ((X : ℝ) - (X₀ : ℝ) - (Bad1.card : ℝ) - (Bad2.card : ℝ)) / (X : ℝ) ≤
          ((S ∩ Set.Iio X).ncard : ℝ) / (X : ℝ) :=
        div_le_div_of_nonneg_right hncard_lb_r hX_rpos.le
      have h2 : ((X : ℝ) - (X₀ : ℝ) - (Bad1.card : ℝ) - (Bad2.card : ℝ)) / (X : ℝ) =
          1 - ((X₀ : ℝ) / (X : ℝ) + (Bad1.card : ℝ) / (X : ℝ) + (Bad2.card : ℝ) / (X : ℝ)) := by
        field_simp; ring
      linarith
    linarith
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

end OMA.Erdos731

theorem OMA.solution : type_of% @Erdos731.erdos_731.variants.egrs75 :=
  OMA.Erdos731.erdos_731_egrs75_proof
