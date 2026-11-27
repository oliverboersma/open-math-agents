import FormalConjectures.OEIS.«4290»

/-!
# Exact Repunit Formula and Structural Reduction for `OeisA4290.conjecture`

Credit: @cybergenesis621

Formalizes the baseline repunit identity stated in `FormalConjectures/OEIS/4290.lean`,
`OeisA4290.a (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9` for all `k : ℕ`, via base-`10^k` block
decomposition, and reduces `OeisA4290.conjecture` to existence of a `{0, 1}`-digit multiple
strictly below `(10 ^ (9 * k) - 1) / 9` in two complementary arithmetic regimes:
- `H1`: Positive integers `n < 10^k - 1` coprime to `10`.
- `H2`: Positive integers `n < 10^k - 1` sharing a prime factor with `10`.
-/

namespace OMA.R_OeisA4290_conjecture_R1

open OeisA4290

private lemma nine_dvd_ten_pow_sub_one (m : ℕ) : 9 ∣ 10 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ r ih =>
    rcases ih with ⟨q, hq⟩
    have hge : 1 ≤ 10 ^ r := Nat.one_le_pow r 10 (by decide)
    refine ⟨10 * q + 1, ?_⟩
    rw [pow_succ']
    omega

private lemma nine_mul_repunit (m : ℕ) : 9 * ((10 ^ m - 1) / 9) = 10 ^ m - 1 :=
  Nat.mul_div_cancel' (nine_dvd_ten_pow_sub_one m)

private lemma repunit_succ (m : ℕ) :
    (10 ^ (m + 1) - 1) / 9 = 10 * ((10 ^ m - 1) / 9) + 1 := by
  have h1 := nine_mul_repunit (m + 1)
  have h2 := nine_mul_repunit m
  have hge : 1 ≤ 10 ^ m := Nat.one_le_pow m 10 (by decide)
  rw [pow_succ'] at h1
  omega

private lemma repunit_pos {m : ℕ} (hm : 0 < m) : 0 < (10 ^ m - 1) / 9 := by
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  rw [repunit_succ]
  omega

private lemma digits_repunit (m : ℕ) :
    Nat.digits 10 ((10 ^ m - 1) / 9) = List.replicate m 1 := by
  induction m with
  | zero => simp
  | succ r ih =>
    rw [repunit_succ, List.replicate_succ]
    have hpos : 0 < 10 * ((10 ^ r - 1) / 9) + 1 := by omega
    rw [Nat.digits_def' (by decide) hpos]
    have hmod : (10 * ((10 ^ r - 1) / 9) + 1) % 10 = 1 := by omega
    have hdiv : (10 * ((10 ^ r - 1) / 9) + 1) / 10 = (10 ^ r - 1) / 9 := by omega
    rw [hmod, hdiv, ih]

private lemma repunit_digits_01 (m : ℕ) :
    ∀ d ∈ Nat.digits 10 ((10 ^ m - 1) / 9), d = 0 ∨ d = 1 := by
  intro d hd
  rw [digits_repunit, List.mem_replicate] at hd
  exact Or.inr hd.2

private lemma ten_pow_sub_one_dvd_repunit_nine (k : ℕ) :
    10 ^ k - 1 ∣ (10 ^ (9 * k) - 1) / 9 := by
  let B := 10 ^ k
  have hB : 1 ≤ B := Nat.one_le_pow k 10 (by decide)
  let S := ∑ j ∈ Finset.range 9, B ^ j
  have hgeom : (B - 1) * S = B ^ 9 - 1 := by
    have h1 : S * (B - 1) = B ^ 9 - 1 := by
      dsimp [S]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero]
      have hB1 : 1 ≤ B := hB
      have hB2 : B ≤ B ^ 2 := by nlinarith
      zify [hB, Nat.one_le_pow 9 B (by omega)]
      ring
    linarith
  have hS_mod9 : S % 9 = 0 := by
    have hB_mod : B % 9 = 1 := by
      have h9 := nine_dvd_ten_pow_sub_one k
      rcases h9 with ⟨q, hq⟩
      have : B = 9 * q + 1 := by omega
      omega
    have hpow_mod : ∀ j : ℕ, (B ^ j) % 9 = 1 := by
      intro j
      induction j with
      | zero => simp
      | succ r ih =>
        rw [pow_succ, Nat.mul_mod, ih, hB_mod]
    dsimp [S]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h0 := hpow_mod 0
    have h1 := hpow_mod 1
    have h2 := hpow_mod 2
    have h3 := hpow_mod 3
    have h4 := hpow_mod 4
    have h5 := hpow_mod 5
    have h6 := hpow_mod 6
    have h7 := hpow_mod 7
    have h8 := hpow_mod 8
    omega
  have h9S : 9 ∣ S := Nat.dvd_of_mod_eq_zero hS_mod9
  rcases h9S with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  have h9r : 9 * ((10 ^ (9 * k) - 1) / 9) = 10 ^ (9 * k) - 1 := nine_mul_repunit (9 * k)
  have hpow9 : 10 ^ (9 * k) = B ^ 9 := by dsimp [B]; rw [← pow_mul, mul_comm]
  have hmul : 9 * ((10 ^ (9 * k) - 1) / 9) = 9 * ((10 ^ k - 1) * q) := by
    calc 9 * ((10 ^ (9 * k) - 1) / 9) = 10 ^ (9 * k) - 1 := h9r
      _ = B ^ 9 - 1 := by rw [hpow9]
      _ = (B - 1) * S := hgeom.symm
      _ = (B - 1) * (9 * q) := by rw [hq]
      _ = 9 * ((10 ^ k - 1) * q) := by dsimp [B]; ring
  omega

private lemma le_repunit_of_digits_01 :
    ∀ k x : ℕ, x < 10 ^ k → (∀ d ∈ Nat.digits 10 x, d = 0 ∨ d = 1) → x ≤ (10 ^ k - 1) / 9 := by
  intro k
  induction k with
  | zero =>
    intro x hx _
    simp at hx
    omega
  | succ r ih =>
    intro x hx hdig
    rcases Nat.eq_zero_or_pos x with rfl | hx_pos
    · exact Nat.zero_le _
    · have hd := Nat.digits_def' (by decide : 2 ≤ 10) hx_pos
      have hmod01 : x % 10 = 0 ∨ x % 10 = 1 := by
        apply hdig (x % 10)
        rw [hd]
        exact List.Mem.head _
      have hdiv01 : ∀ d ∈ Nat.digits 10 (x / 10), d = 0 ∨ d = 1 := by
        intro d hd'
        apply hdig d
        rw [hd]
        exact List.Mem.tail _ hd'
      have hdiv_lt : x / 10 < 10 ^ r := by
        rw [pow_succ'] at hx
        omega
      have hdiv_le : x / 10 ≤ (10 ^ r - 1) / 9 := ih (x / 10) hdiv_lt hdiv01
      rw [repunit_succ]
      omega

private lemma mod_div_digits_01 {k : ℕ} :
    ∀ x : ℕ, (∀ d ∈ Nat.digits 10 x, d = 0 ∨ d = 1) →
      (∀ d ∈ Nat.digits 10 (x % 10 ^ k), d = 0 ∨ d = 1) ∧
      (∀ d ∈ Nat.digits 10 (x / 10 ^ k), d = 0 ∨ d = 1) := by
  induction k with
  | zero =>
    intro x hx
    exact ⟨by simp [Nat.mod_one], by simpa using hx⟩
  | succ r ih =>
    intro x hx
    rcases Nat.eq_zero_or_pos x with rfl | hx_pos
    · simp
    · have hd := Nat.digits_def' (by decide : 2 ≤ 10) hx_pos
      have hmod10 : x % 10 = 0 ∨ x % 10 = 1 :=
        hx (x % 10) (by rw [hd]; exact List.Mem.head _)
      have hdiv10 : ∀ d ∈ Nat.digits 10 (x / 10), d = 0 ∨ d = 1 := fun d hd' =>
        hx d (by rw [hd]; exact List.Mem.tail _ hd')
      obtain ⟨hrm, hrd⟩ := ih (x / 10) hdiv10
      have hdiv_eq : x / 10 ^ (r + 1) = (x / 10) / 10 ^ r := by
        rw [pow_succ', Nat.div_div_eq_div_mul]
      have hmod_eq : x % 10 ^ (r + 1) = 10 * ((x / 10) % 10 ^ r) + x % 10 := by
        have h1 := Nat.div_add_mod x 10
        have h2 := Nat.div_add_mod (x / 10) (10 ^ r)
        have h3 := Nat.div_add_mod x (10 ^ (r + 1))
        have h4 : 10 ^ (r + 1) * (x / 10 ^ (r + 1)) = 10 * (10 ^ r * ((x / 10) / 10 ^ r)) := by
          rw [hdiv_eq, pow_succ', mul_assoc]
        omega
      refine ⟨?_, by rw [hdiv_eq]; exact hrd⟩
      rw [hmod_eq]
      intro d hd'
      rcases Nat.eq_zero_or_pos (10 * ((x / 10) % 10 ^ r) + x % 10) with hzero | hpos
      · rw [hzero, Nat.digits_zero] at hd'; simp at hd'
      · rw [Nat.digits_def' (by decide : 2 ≤ 10) hpos] at hd'
        have hm1 : (10 * ((x / 10) % 10 ^ r) + x % 10) % 10 = x % 10 := by omega
        have hd1 : (10 * ((x / 10) % 10 ^ r) + x % 10) / 10 = (x / 10) % 10 ^ r := by omega
        rw [hm1, hd1] at hd'
        rcases List.mem_cons.mp hd' with rfl | htail
        · exact hmod10
        · exact hrm d htail

private lemma digits_base_pow_le_repunit {k : ℕ} (hk : 1 ≤ k) :
    ∀ x : ℕ, (∀ d ∈ Nat.digits 10 x, d = 0 ∨ d = 1) →
      ∀ b ∈ Nat.digits (10 ^ k) x, b ≤ (10 ^ k - 1) / 9 := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hx b hb
    rcases Nat.eq_zero_or_pos x with rfl | hx_pos
    · simp at hb
    · have hbase : 2 ≤ 10 ^ k := by
        calc 2 ≤ 10 ^ 1 := by decide
          _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
      rw [Nat.digits_def' hbase hx_pos] at hb
      obtain ⟨hm01, hd01⟩ := mod_div_digits_01 (k := k) x hx
      rcases List.mem_cons.mp hb with rfl | htail
      · exact le_repunit_of_digits_01 k (x % 10 ^ k) (Nat.mod_lt x (Nat.pow_pos (by decide))) hm01
      · exact ih (x / 10 ^ k) (Nat.div_lt_self hx_pos (by omega)) hd01 b htail

private lemma digits_sum_mod_eq {B : ℕ} (hB : 2 ≤ B) :
    ∀ x : ℕ, x % (B - 1) = (Nat.digits B x).sum % (B - 1) := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx_pos
    · simp
    · rw [Nat.digits_def' hB hx_pos, List.sum_cons]
      have hlt : x / B < x := Nat.div_lt_self hx_pos (by omega)
      have hih := ih (x / B) hlt
      have hdiv : x = (x / B) * (B - 1) + (x / B + x % B) := by
        have := Nat.div_add_mod x B
        have h1 : B * (x / B) = (x / B) * (B - 1) + x / B := by
          obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        omega
      calc x % (B - 1)
          = ((x / B) * (B - 1) + (x / B + x % B)) % (B - 1) := by rw [← hdiv]
        _ = (x / B + x % B) % (B - 1) := by rw [Nat.mul_add_mod_self_right]
        _ = ((x / B) % (B - 1) + (x % B) % (B - 1)) % (B - 1) := by rw [Nat.add_mod]
        _ = ((Nat.digits B (x / B)).sum % (B - 1) + (x % B) % (B - 1)) % (B - 1) := by rw [hih]
        _ = ((Nat.digits B (x / B)).sum + x % B) % (B - 1) := by rw [← Nat.add_mod]
        _ = (x % B + (Nat.digits B (x / B)).sum) % (B - 1) := by rw [add_comm]

private lemma ofDigits_eq_repunit_of_all_eq {k : ℕ} (_hk : 1 ≤ k) :
    ∀ l : List ℕ, l.length = 9 → (∀ b ∈ l, b = (10 ^ k - 1) / 9) →
      Nat.ofDigits (10 ^ k) l = (10 ^ (9 * k) - 1) / 9 := by
  intro l hlen hall
  have hrep : l = List.replicate 9 ((10 ^ k - 1) / 9) :=
    List.eq_replicate_iff.mpr ⟨hlen, hall⟩
  rw [hrep]
  have h9 : 9 * Nat.ofDigits (10 ^ k) (List.replicate 9 ((10 ^ k - 1) / 9)) = 10 ^ (9 * k) - 1 := by
    simp only [List.replicate_succ, List.replicate_zero, Nat.ofDigits_cons, Nat.ofDigits_nil,
      mul_zero, add_zero]
    have h9k := nine_mul_repunit k
    have h1 : 1 ≤ 10 ^ k := Nat.one_le_pow k 10 (by decide)
    have hpow : 10 ^ (9 * k) = (10 ^ k) ^ 9 := by rw [← pow_mul, mul_comm]
    rw [hpow]
    zify [h1, Nat.one_le_pow 9 (10 ^ k) (by omega)] at h9k ⊢
    set B : ℤ := (10 ^ k : ℤ)
    set r : ℤ := (B - 1) / 9
    have hfact : 9 * (r + B * (r + B * (r + B * (r + B * (r + B * (r + B * (r + B * (r + B * r)))))))) =
        (9 * r) * (1 + B + B ^ 2 + B ^ 3 + B ^ 4 + B ^ 5 + B ^ 6 + B ^ 7 + B ^ 8) := by ring
    rw [hfact, h9k]
    ring
  have h9r := nine_mul_repunit (9 * k)
  omega

private lemma list_mem_le_sum : ∀ {xs : List ℕ} {b : ℕ}, b ∈ xs → b ≤ xs.sum
  | [], _, hb => absurd hb (by simp)
  | y :: ys, b, hb => by
    simp only [List.sum_cons]
    rcases List.mem_cons.mp hb with rfl | htail
    · omega
    · have := list_mem_le_sum htail; omega

private lemma list_sum_le_len_mul : ∀ {xs : List ℕ} {C : ℕ}, (∀ x ∈ xs, x ≤ C) → xs.sum ≤ xs.length * C
  | [], _, _ => by simp
  | y :: ys, C, h => by
    simp only [List.sum_cons, List.length_cons, add_mul, one_mul]
    have hy : y ≤ C := h y (List.Mem.head _)
    have hys : ys.sum ≤ ys.length * C := list_sum_le_len_mul fun z hz => h z (List.Mem.tail _ hz)
    omega

private lemma a_ten_pow_sub_one (k : ℕ) :
    a (10 ^ k - 1) = (10 ^ (9 * k) - 1) / 9 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using OeisA4290.a_0
  · have hbase : 2 ≤ 10 ^ k := by
      calc 2 ≤ 10 ^ 1 := by decide
        _ ≤ 10 ^ k := Nat.pow_le_pow_right (by decide) hk
    have hmem : (10 ^ (9 * k) - 1) / 9 ∈
        { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 } :=
      ⟨repunit_pos (by omega), ten_pow_sub_one_dvd_repunit_nine k, repunit_digits_01 (9 * k)⟩
    have hmin : ∀ m ∈ { m : ℕ | 0 < m ∧ (10 ^ k - 1) ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1 },
        (10 ^ (9 * k) - 1) / 9 ≤ m := by
      intro m ⟨hm_pos, hdvd, hdig⟩
      let L := Nat.digits (10 ^ k) m
      have hL_le : ∀ b ∈ L, b ≤ (10 ^ k - 1) / 9 := digits_base_pow_le_repunit hk m hdig
      have hsum_mod : L.sum % (10 ^ k - 1) = 0 := by
        rw [← digits_sum_mod_eq hbase m]
        exact Nat.mod_eq_zero_of_dvd hdvd
      have hL_nonempty : L ≠ [] := by
        intro hnil
        have hm0 : m = 0 := by
          rw [← Nat.ofDigits_digits (10 ^ k) m]
          change Nat.ofDigits (10 ^ k) L = 0
          rw [hnil]; rfl
        omega
      have hsum_pos : 0 < L.sum := by
        by_contra h0
        have hsum0 : L.sum = 0 := by omega
        have hall0 : ∀ b ∈ L, b = 0 := by
          intro b hb
          have hle := list_mem_le_sum hb
          omega
        have hlast_ne0 : L.getLast hL_nonempty ≠ 0 :=
          Nat.getLast_digit_ne_zero (10 ^ k) hm_pos.ne'
        exact hlast_ne0 (hall0 _ (List.getLast_mem hL_nonempty))
      have hsum_ge : 10 ^ k - 1 ≤ L.sum :=
        Nat.le_of_dvd hsum_pos (Nat.dvd_of_mod_eq_zero hsum_mod)
      have hsum_ub : L.sum ≤ L.length * ((10 ^ k - 1) / 9) := list_sum_le_len_mul hL_le
      have h9rk : 9 * ((10 ^ k - 1) / 9) = 10 ^ k - 1 := nine_mul_repunit k
      have hrk_pos : 0 < (10 ^ k - 1) / 9 := repunit_pos hk
      have hlen_ge9 : 9 ≤ L.length := by
        have : 9 * ((10 ^ k - 1) / 9) ≤ L.length * ((10 ^ k - 1) / 9) := by omega
        exact Nat.le_of_mul_le_mul_right this hrk_pos
      rcases eq_or_lt_of_le hlen_ge9 with hlen9 | hlen_gt9
      · have hall_eq : ∀ b ∈ L, b = (10 ^ k - 1) / 9 := by
          intro b hb
          by_contra hne
          have hlt : b < (10 ^ k - 1) / 9 := lt_of_le_of_ne (hL_le b hb) hne
          have hstrict : L.sum < L.length * ((10 ^ k - 1) / 9) := by
            have hlt_aux : ∀ xs : List ℕ, (∀ x ∈ xs, x ≤ (10 ^ k - 1) / 9) →
                (∃ x ∈ xs, x < (10 ^ k - 1) / 9) → xs.sum < xs.length * ((10 ^ k - 1) / 9) := by
              intro xs
              induction xs with
              | nil => intro _ ⟨_, hx, _⟩; simp at hx
              | cons y ys ihy =>
                intro hle' hex'
                simp only [List.sum_cons, List.length_cons, add_mul, one_mul]
                have hy_le : y ≤ (10 ^ k - 1) / 9 := hle' y (List.Mem.head _)
                have hys_le : ∀ z ∈ ys, z ≤ (10 ^ k - 1) / 9 := fun z hz => hle' z (List.Mem.tail _ hz)
                rcases hex' with ⟨z, hz, hzlt⟩
                rcases List.mem_cons.mp hz with rfl | hztail
                · have hys_sum : ys.sum ≤ ys.length * ((10 ^ k - 1) / 9) := list_sum_le_len_mul hys_le
                  omega
                · have := ihy hys_le ⟨z, hztail, hzlt⟩
                  omega
            exact hlt_aux L hL_le ⟨b, hb, hlt⟩
          rw [← hlen9] at hstrict
          omega
        have hm_eq : m = (10 ^ (9 * k) - 1) / 9 := by
          rw [← Nat.ofDigits_digits (10 ^ k) m]
          exact ofDigits_eq_repunit_of_all_eq hk L hlen9.symm hall_eq
        omega
      · have hlen_ge10 : 10 ≤ L.length := by omega
        have hpow_le_mul : (10 ^ k) ^ L.length ≤ 10 ^ k * m :=
          Nat.base_pow_length_digits_le (10 ^ k) m (by omega) hm_pos.ne'
        have hpow10 : 10 ^ k * (10 ^ k) ^ 9 ≤ (10 ^ k) ^ L.length := by
          have : 10 ^ k * (10 ^ k) ^ 9 = (10 ^ k) ^ 10 := by rw [← pow_succ']
          rw [this]
          exact Nat.pow_le_pow_right (by omega) hlen_ge10
        have hm_ge : (10 ^ k) ^ 9 ≤ m :=
          Nat.le_of_mul_le_mul_left (le_trans hpow10 hpow_le_mul) (Nat.pow_pos (by decide))
        have h9r := nine_mul_repunit (9 * k)
        have hpow_eq : (10 ^ k) ^ 9 = 10 ^ (9 * k) := by rw [← pow_mul, mul_comm]
        omega
    exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨(10 ^ (9 * k) - 1) / 9, hmem⟩ hmin)

/-- Every positive integer `n < 10^k - 1` coprime to `10` admits a positive `{0, 1}`-digit
multiple strictly smaller than `(10 ^ (9 * k) - 1) / 9`. -/
def H1 : Prop :=
  ∀ k : ℕ, ∀ n : ℕ, 0 < n → n < 10 ^ k - 1 → Nat.Coprime n 10 →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- Every positive integer `n < 10^k - 1` sharing a factor with `10` admits a positive
`{0, 1}`-digit multiple strictly smaller than `(10 ^ (9 * k) - 1) / 9`. -/
def H2 : Prop :=
  ∀ k : ℕ, ∀ n : ℕ, 0 < n → n < 10 ^ k - 1 → ¬ Nat.Coprime n 10 →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

theorem main : H1 → H2 → type_of% @OeisA4290.conjecture := by
  intro h1 h2 k n hn_lt
  rw [a_ten_pow_sub_one k]
  rcases Nat.eq_zero_or_pos n with rfl | hn_pos
  · rw [OeisA4290.a_0]
    have hk_pos : 0 < k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      rw [hk0] at hn_lt
      simp at hn_lt
    exact repunit_pos (by omega)
  · by_cases hcop : Nat.Coprime n 10
    · obtain ⟨m, hmlt, hm⟩ := h1 k n hn_pos hn_lt hcop
      exact lt_of_le_of_lt (Nat.sInf_le hm) hmlt
    · obtain ⟨m, hmlt, hm⟩ := h2 k n hn_pos hn_lt hcop
      exact lt_of_le_of_lt (Nat.sInf_le hm) hmlt

end OMA.R_OeisA4290_conjecture_R1
