import OMAStatements.S_oeis_a318291

namespace OMA.S_oeis_a318291

/-- The covering property over one period extends to every k >= 1. -/
theorem cover_all (R L : ℕ) (Qs : List ℕ) (hL : 0 < L) (hper : ∀ q ∈ Qs, 2 ^ L % q = 1 ∧ 1 < q)
    (hbase : ∀ i < L, ∃ q ∈ Qs, R * 2 ^ (i + 1) % q = 1) (k : ℕ) (hk : 1 ≤ k) :
    ∃ q ∈ Qs, R * 2 ^ k % q = 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h : k ≤ L
    · have := hbase (k - 1) (by omega)
      rwa [show k - 1 + 1 = k by omega] at this
    · obtain ⟨q, hq, h1⟩ := ih (k - L) (by omega) (by omega)
      refine ⟨q, hq, ?_⟩
      have hL := (hper q hq).1
      rw [show k = (k - L) + L by omega, pow_add, ← mul_assoc, Nat.mul_mod, hL, mul_one,
        Nat.mod_mod, h1]

/-- The family of multipliers j given by one certificate. -/
theorem family (p R L : ℕ) (Qs : List ℕ) (hp : p.Prime) (hpQ : Qs.prod % p ≠ 0) (hL : 0 < L)
    (hper : ∀ q ∈ Qs, 2 ^ L % q = 1 ∧ 1 < q)
    (hbase : ∀ i < L, ∃ q ∈ Qs, R * 2 ^ (i + 1) % q = 1) (s : ℕ) :
    ¬ p ∣ p * R + Qs.prod * (p * s + 1) ∧
      ∀ k, 0 < k → 1 < (p * R + Qs.prod * (p * s + 1)) * 2 ^ k - p ∧
        ¬ ((p * R + Qs.prod * (p * s + 1)) * 2 ^ k - p).Prime := by
  set Q := Qs.prod with hQdef
  set j := p * R + Q * (p * s + 1) with hj
  constructor
  · intro hdvd
    have e : j = p * (R + Q * s) + Q := by rw [hj]; ring
    have : j % p = Q % p := by rw [e, Nat.mul_add_mod]
    exact hpQ (by rw [← this]; exact Nat.mod_eq_zero_of_dvd hdvd)
  · intro k hk
    obtain ⟨q, hq, h1⟩ := cover_all R L Qs hL hper hbase k hk
    have hq1 := (hper q hq).2
    have hqQ : q ∣ Q := List.dvd_prod hq
    have hQpos : 0 < Q := by
      rcases Nat.eq_zero_or_pos Q with h0 | h0
      · exact absurd (by rw [h0]; simp) hpQ
      · exact h0
    have hqle : q ≤ Q := Nat.le_of_dvd hQpos hqQ
    have hp2 := hp.two_le
    have h2k : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have hjQ : Q ≤ Q * (p * s + 1) := Nat.le_mul_of_pos_right Q (by omega)
    have hbig : 2 * j ≤ j * 2 ^ k := by rw [mul_comm 2 j]; exact Nat.mul_le_mul_left j h2k
    have hjge : p + Q ≤ j := by
      have : p ≤ p * R ∨ R = 0 := by
        rcases Nat.eq_zero_or_pos R with h0 | h0
        · right; exact h0
        · left; exact Nat.le_mul_of_pos_right p h0
      rcases this with h | h
      · omega
      · rw [h] at h1
        simp at h1
    have hmod : j * 2 ^ k % q = p % q := by
      have e : j * 2 ^ k = p * (R * 2 ^ k) + Q * ((p * s + 1) * 2 ^ k) := by rw [hj]; ring
      obtain ⟨c, hc⟩ := hqQ
      rw [e, hc, Nat.add_mod, Nat.mul_mod p, h1, mul_one, Nat.mod_mod,
        show q * c * ((p * s + 1) * 2 ^ k) = q * (c * ((p * s + 1) * 2 ^ k)) by ring,
        Nat.mul_mod_right, add_zero, Nat.mod_mod]
    have hdvd : q ∣ j * 2 ^ k - p := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hmod)
    have hlt : q < j * 2 ^ k - p := by omega
    refine ⟨by omega, fun hpr => ?_⟩
    rcases hpr.eq_one_or_self_of_dvd q hdvd with h | h <;> omega

theorem infinite_of_family (p R L : ℕ) (Qs : List ℕ) (hp : p.Prime) (hpQ : Qs.prod % p ≠ 0)
    (hL : 0 < L) (hper : ∀ q ∈ Qs, 2 ^ L % q = 1 ∧ 1 < q)
    (hbase : ∀ i < L, ∃ q ∈ Qs, R * 2 ^ (i + 1) % q = 1) :
    Set.Infinite {j : ℕ | ¬ p ∣ j ∧ ∀ k, 0 < k → 1 < j * 2 ^ k - p ∧ ¬ (j * 2 ^ k - p).Prime} := by
  have hQpos : 0 < Qs.prod := by
    rcases Nat.eq_zero_or_pos Qs.prod with h0 | h0
    · exact absurd (by rw [h0]; simp) hpQ
    · exact h0
  have hp0 := hp.pos
  have hinj : Function.Injective (fun s : ℕ => p * R + Qs.prod * (p * s + 1)) := by
    intro a b hab
    simp only at hab
    have h1 : Qs.prod * (p * a + 1) = Qs.prod * (p * b + 1) := by omega
    have h2 : p * a + 1 = p * b + 1 := Nat.eq_of_mul_eq_mul_left hQpos h1
    have h3 : p * a = p * b := by omega
    exact Nat.eq_of_mul_eq_mul_left hp0 h3
  refine Set.infinite_of_injective_forall_mem hinj (fun s => ?_)
  exact family p R L Qs hp hpQ hL hper hbase s

/-! ## The three certificates -/

def QsA : List ℕ := [3, 5, 7, 13, 17, 241]

theorem perA : ∀ q ∈ QsA, 2 ^ 24 % q = 1 ∧ 1 < q := by decide

theorem baseA : ∀ i < 24, ∃ q ∈ QsA, 509203 * 2 ^ (i + 1) % q = 1 := by decide +kernel

def QsB : List ℕ := [3, 11, 19, 31, 37, 61, 73, 97, 109, 151, 181, 257, 331, 433, 631, 673, 1321,
  23311, 38737, 54001, 61681, 18837001, 29247661, 394783681, 4278255361, 4562284561,
  487824887233, 469775495062434961]

def RB : ℕ := 47331502034298038266469607062156315672532639789589194455825983409180959488514692191682083566205589100446566213470055374222724

set_option maxRecDepth 100000 in
theorem perB : ∀ q ∈ QsB, 2 ^ 720 % q = 1 ∧ 1 < q := by decide +kernel

set_option maxRecDepth 100000 in
theorem baseB : ∀ i < 720, ∃ q ∈ QsB, RB * 2 ^ (i + 1) % q = 1 := by decide +kernel

def QsC : List ℕ := [5, 7, 11, 13, 17, 19, 31, 37, 61, 73, 109, 151, 181, 241, 331, 631, 1321, 23311,
  38737, 61681, 18837001, 469775495062434961]

def RC : ℕ := 777439995319871612058281705741225133835804367447418519800834158970598

set_option maxRecDepth 100000 in
theorem perC : ∀ q ∈ QsC, 2 ^ 360 % q = 1 ∧ 1 < q := by decide +kernel

set_option maxRecDepth 100000 in
theorem baseC : ∀ i < 360, ∃ q ∈ QsC, RC * 2 ^ (i + 1) % q = 1 := by decide +kernel

/-- An odd prime outside 3, 5, 7, 13, 17, 241 does not divide their product. -/
theorem prodA_mod (p : ℕ) (hp : p.Prime) (h : p ∉ QsA) : QsA.prod % p ≠ 0 := by
  intro h0
  have hdvd : p ∣ 3 * (5 * (7 * (13 * (17 * 241)))) := by
    have : QsA.prod = 3 * (5 * (7 * (13 * (17 * 241)))) := by decide
    rw [← this]
    exact Nat.dvd_of_mod_eq_zero h0
  have eq : ∀ r, r.Prime → p ∣ r → p = r := fun r hr hd => (Nat.prime_dvd_prime_iff_eq hp hr).mp hd
  apply h
  simp only [QsA, List.mem_cons, List.not_mem_nil, or_false]
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h
  · left; exact eq 3 (by norm_num) h3
  rcases (Nat.Prime.dvd_mul hp).mp h with h5 | h
  · right; left; exact eq 5 (by norm_num) h5
  rcases (Nat.Prime.dvd_mul hp).mp h with h7 | h
  · right; right; left; exact eq 7 (by norm_num) h7
  rcases (Nat.Prime.dvd_mul hp).mp h with h13 | h
  · right; right; right; left; exact eq 13 (by norm_num) h13
  rcases (Nat.Prime.dvd_mul hp).mp h with h17 | h241
  · right; right; right; right; left; exact eq 17 (by norm_num) h17
  · right; right; right; right; right; exact eq 241 (by norm_num) h241

/-- Musatov's conjecture: for every odd prime p there are infinitely many j, not multiples of p,
with j*2^k - p composite (greater than 1 and not prime) for every k > 0. -/
theorem conjecture (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Set.Infinite {j : ℕ | ¬ p ∣ j ∧ ∀ k, 0 < k → 1 < j * 2 ^ k - p ∧ ¬ (j * 2 ^ k - p).Prime} := by
  by_cases h3 : p = 3
  · subst h3
    exact infinite_of_family 3 RC 360 QsC hp (by decide) (by norm_num) perC baseC
  by_cases hB : p ∈ [5, 7, 13, 17, 241]
  · have hmod : QsB.prod % p ≠ 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
      rcases hB with rfl | rfl | rfl | rfl | rfl <;> decide
    exact infinite_of_family p RB 720 QsB hp hmod (by norm_num) perB baseB
  · have hA : p ∉ QsA := by
      simp only [QsA, List.mem_cons, List.not_mem_nil, or_false]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hB
      omega
    exact infinite_of_family p 509203 24 QsA hp (prodA_mod p hp hA) (by norm_num) perA baseA

end OMA.S_oeis_a318291

theorem OMA.solution : type_of% @OMA.S_oeis_a318291.main :=
  fun p hp hp2 => OMA.S_oeis_a318291.conjecture p hp hp2
