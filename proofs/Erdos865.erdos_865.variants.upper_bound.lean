import FormalConjectures.ErdosProblems.«865»

namespace OMA
namespace Chn

open Finset Filter

/-! ## 2-adic valuation and odd part -/

/-- The 2-adic valuation. -/
def dv (m : ℕ) : ℕ := padicValNat 2 m

/-- The odd part. -/
def od (m : ℕ) : ℕ := m / 2 ^ dv m

lemma dv_dvd (m : ℕ) : 2 ^ dv m ∣ m := pow_padicValNat_dvd

lemma dv_succ_not_dvd {m : ℕ} (hm : m ≠ 0) : ¬ 2 ^ (dv m + 1) ∣ m :=
  pow_succ_padicValNat_not_dvd hm

lemma od_mul (m : ℕ) : od m * 2 ^ dv m = m := Nat.div_mul_cancel (dv_dvd m)

lemma od_le (m : ℕ) : od m ≤ m := Nat.div_le_self m _

lemma od_pos {m : ℕ} (hm : m ≠ 0) : 0 < od m := Nat.pos_of_ne_zero fun h => hm (by
  rw [← od_mul m, h, Nat.zero_mul])

lemma od_not_two_dvd {m : ℕ} (hm : m ≠ 0) : ¬ 2 ∣ od m := by
  intro h2
  refine dv_succ_not_dvd hm ?_
  have h3 : 2 ^ dv m * 2 ∣ 2 ^ dv m * od m := Nat.mul_dvd_mul_left _ h2
  rw [← Nat.pow_succ, Nat.mul_comm, od_mul] at h3
  exact h3

lemma dv_eq_zero {u : ℕ} (hu : ¬ 2 ∣ u) : dv u = 0 := padicValNat.eq_zero_of_not_dvd hu

lemma dv_two_pow (t : ℕ) : dv (2 ^ t) = t := by
  unfold dv
  rw [padicValNat.pow, padicValNat_self, mul_one]

lemma dv_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : dv (a * b) = dv a + dv b :=
  padicValNat.mul ha hb

lemma dv_ch {u e : ℕ} (hu : u ≠ 0) (hu2 : ¬ 2 ∣ u) : dv (u * 2 ^ e) = e := by
  have h1 : u * 2 ^ e ≠ 0 :=
    Nat.mul_ne_zero hu (Nat.two_pow_pos e).ne'
  rw [dv_mul hu (Nat.two_pow_pos e).ne', dv_eq_zero hu2, dv_two_pow]
  omega

/-! ## Basic log and divisibility transfer lemmas -/

lemma pow_le_of_log2_le {M e : ℕ} (hM : M ≠ 0) (h : e ≤ Nat.log 2 M) : 2 ^ e ≤ M := by
  have h1 : 2 ^ e ≤ 2 ^ Nat.log 2 M := Nat.pow_le_pow_right (by norm_num) h
  have h2 : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 hM
  omega

lemma log2_le_of_pow_le {M e : ℕ} (h : 2 ^ e ≤ M) : e ≤ Nat.log 2 M := by
  have h2 : (0:ℕ) < 2 ^ e := Nat.two_pow_pos e
  by_cases he : e = 0
  · omega
  · by_contra hcon
    push_neg at hcon
    have hM : M ≠ 0 := by omega
    have h1 := (Nat.log_lt_iff_lt_pow (by norm_num) hM).1 hcon
    omega

lemma mul_le_of_div_le {u M e : ℕ} (hu : 0 < u) (h : 2 ^ e ≤ M / u) : u * 2 ^ e ≤ M := by
  have h1 : 2 ^ e * u ≤ M := (Nat.le_div_iff_mul_le hu).1 h
  rw [Nat.mul_comm]
  exact h1

lemma div_le_of_mul_le {u M e : ℕ} (hu : 0 < u) (h : u * 2 ^ e ≤ M) : 2 ^ e ≤ M / u := by
  refine (Nat.le_div_iff_mul_le hu).2 ?_
  rw [Nat.mul_comm]
  exact h

lemma div_pos_of_le {u N : ℕ} (hu : 0 < u) (huN : u ≤ N) : 0 < N / u :=
  Nat.div_pos huN hu

/-! ## Chains -/

/-- The chain `C_u` for a base `u`: the elements `u * 2^e ≤ N`. -/
def ch (N u : ℕ) : Finset ℕ :=
  (Finset.range (Nat.log 2 (N / u) + 1)).image (fun e => u * 2 ^ e)

lemma ch_card {N u : ℕ} (hu : 0 < u) : (ch N u).card = Nat.log 2 (N / u) + 1 := by
  unfold ch
  have h1 : ((Finset.range (Nat.log 2 (N / u) + 1)).image (fun e => u * 2 ^ e)).card =
      (Finset.range (Nat.log 2 (N / u) + 1)).card :=
    Finset.card_image_of_injOn (by
      intro a _ b _ hab
      have h2 := Nat.eq_of_mul_eq_mul_left hu hab
      exact Nat.pow_right_injective (by norm_num) h2)
  rw [h1, Finset.card_range]

lemma mem_ch {N u e : ℕ} (hu : 0 < u) (huN : u ≤ N) :
    u * 2 ^ e ∈ ch N u ↔ u * 2 ^ e ≤ N := by
  have hNu : N / u ≠ 0 := (div_pos_of_le hu huN).ne'
  unfold ch
  rw [Finset.mem_image]
  constructor
  · rintro ⟨e', he', hee⟩
    have h1 : e' ≤ Nat.log 2 (N / u) := by
      have := Finset.mem_range.1 he'
      omega
    have h2 : 2 ^ e' ≤ N / u := pow_le_of_log2_le hNu h1
    have h3 : u * 2 ^ e' ≤ N := mul_le_of_div_le hu h2
    have h4 : u * 2 ^ e' = u * 2 ^ e := hee
    rw [← h4]
    exact h3
  · intro hN
    have h2 : 2 ^ e ≤ N / u := div_le_of_mul_le hu hN
    have h3 : e ≤ Nat.log 2 (N / u) := log2_le_of_pow_le h2
    exact ⟨e, Finset.mem_range.2 (by omega), rfl⟩

/-- Every `m ∈ [1, N]` lies in the chain of its odd part. -/
lemma mem_ch_of_mem_Icc {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    m ∈ ch N (od m) := by
  have hm0 : m ≠ 0 := by omega
  have hu : 0 < od m := od_pos hm0
  have huN : od m ≤ N := Nat.le_trans (od_le m) hmN
  have hle : od m * 2 ^ dv m ≤ N := by rw [od_mul m]; exact hmN
  have hgoal : od m * 2 ^ dv m ∈ ch N (od m) := (mem_ch hu huN).2 hle
  rw [od_mul m] at hgoal
  exact hgoal

/-! ## Position-set combinatorics -/

/-- Bound for a set of positions with no two adjacent. -/
lemma indep_bound {L : ℕ} (P : Finset ℕ) (hPL : ∀ e ∈ P, e < L)
    (hind : ∀ e ∈ P, e + 1 < L → e + 1 ∉ P) :
    P.card ≤ (L + 1) / 2 := by
  classical
  set evens := (Finset.range ((L + 1) / 2)).image (fun j => 2 * j) with hev
  have hcard_evens : evens.card = (L + 1) / 2 := by
    have h1 := Finset.card_image_of_injOn
      (f := fun j => 2 * j) (s := Finset.range ((L + 1) / 2)) (by
        intro a _ b _ hab
        have h2 : 2 * a = 2 * b := hab
        omega)
    rw [h1, Finset.card_range]
  have hsub : P.image (fun e => 2 * (e / 2)) ⊆ evens := by
    intro x hx
    obtain ⟨e, he, hx2⟩ := Finset.mem_image.1 hx
    have hxe : x = 2 * (e / 2) := by rw [← hx2]
    refine Finset.mem_image.2 ⟨e / 2, Finset.mem_range.2 ?_, ?_⟩
    · have h1 := hPL e he
      omega
    · have h1 : (fun j => 2 * j) (e / 2) = x := by rw [hxe]
      exact h1
  have hinj : ∀ e₁ ∈ P, ∀ e₂ ∈ P, 2 * (e₁ / 2) = 2 * (e₂ / 2) → e₁ = e₂ := by
    intro e₁ h₁ e₂ h₂ heq
    by_contra hne
    have hsame : e₁ / 2 = e₂ / 2 := by omega
    rcases Nat.lt_or_ge e₁ e₂ with hlt | hge
    · have h3 : e₂ = e₁ + 1 := by omega
      have h4 : e₁ + 1 < L := by
        have := hPL e₂ h₂
        omega
      exact hind e₁ h₁ h4 (by rw [← h3]; exact h₂)
    · have h3 : e₁ = e₂ + 1 := by omega
      have h4 : e₂ + 1 < L := by
        have := hPL e₁ h₁
        omega
      exact hind e₂ h₂ h4 (by rw [← h3]; exact h₁)
  have hcard1 : P.card = (P.image (fun e => 2 * (e / 2))).card :=
    (Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact hinj a ha b hb hab)).symm
  have hcard2 := Finset.card_le_card hsub
  have hcard_evens' := hcard_evens
  omega

/-- Forcing: in an odd-length path, a maximal independent set of positions
contains all even positions. -/
lemma indep_forcing {L : ℕ} (hL : L % 2 = 1) (P : Finset ℕ) (hPL : ∀ e ∈ P, e < L)
    (hind : ∀ e ∈ P, e + 1 < L → e + 1 ∉ P) (hcard : (L + 1) / 2 ≤ P.card) :
    ∀ e, e < L → e % 2 = 0 → e ∈ P := by
  classical
  have hbound := indep_bound P hPL hind
  have hcard_eq : P.card = (L + 1) / 2 := le_antisymm hbound hcard
  set t := (L - 1) / 2 with ht
  -- the collapse map hits every even position
  have hsub : P.image (fun e => 2 * (e / 2)) ⊆
      (Finset.range ((L + 1) / 2)).image (fun j => 2 * j) := by
    intro x hx
    obtain ⟨e, he, hx2⟩ := Finset.mem_image.1 hx
    have hxe : x = 2 * (e / 2) := by rw [← hx2]
    refine Finset.mem_image.2 ⟨e / 2, Finset.mem_range.2 ?_, ?_⟩
    · have h1 := hPL e he
      omega
    · rw [hxe]
  have hcard_img : (P.image (fun e => 2 * (e / 2))).card = (L + 1) / 2 := by
    have h1 : (P.image (fun e => 2 * (e / 2))).card = P.card :=
      Finset.card_image_of_injOn (by
        intro a ha b hb hab
        have h9 : 2 * (a / 2) = 2 * (b / 2) := hab
        have h10 : a / 2 = b / 2 := by omega
        by_contra hne
        rcases Nat.lt_or_ge a b with hlt | hge
        · have h3 : b = a + 1 := by omega
          have h4 : a + 1 < L := by have := hPL b hb; omega
          exact hind a ha h4 (by rw [← h3]; exact hb)
        · have h3 : a = b + 1 := by omega
          have h4 : b + 1 < L := by have := hPL a ha; omega
          exact hind b hb h4 (by rw [← h3]; exact ha))
    rw [h1, hcard_eq]
  have hfull : (P.image (fun e => 2 * (e / 2))) =
      (Finset.range ((L + 1) / 2)).image (fun j => 2 * j) := by
    refine Finset.eq_of_subset_of_card_le hsub ?_
    have h1 := Finset.card_image_of_injOn
      (f := fun j => 2 * j) (s := Finset.range ((L + 1) / 2)) (by
        intro a _ b _ hab
        have h2 : 2 * a = 2 * b := hab
        omega)
    rw [h1, Finset.card_range]
    omega
  -- the witness lemma
  have hwit : ∀ j, j < (L + 1) / 2 → 2 * j ∈ P ∨ 2 * j + 1 ∈ P := by
    intro j hj
    have hmem : 2 * j ∈ (Finset.range ((L + 1) / 2)).image (fun j => 2 * j) :=
      Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩
    rw [← hfull] at hmem
    obtain ⟨e, he, hex⟩ := Finset.mem_image.1 hmem
    have h1 : 2 * (e / 2) = 2 * j := hex
    have h2 : e / 2 = j := by omega
    have h3 : e = 2 * j ∨ e = 2 * j + 1 := by omega
    rcases h3 with h3 | h3
    · exact Or.inl (by rw [← h3]; exact he)
    · exact Or.inr (by rw [← h3]; exact he)
  -- downward induction from the top
  have htop : 2 * t ∈ P := by
    rcases hwit t (by omega) with h | h
    · exact h
    · have h1 := hPL (2 * t + 1) h
      omega
  have hdown : ∀ d, d ≤ t → 2 * (t - d) ∈ P := by
    intro d
    induction d with
    | zero => intro _; exact htop
    | succ d ih =>
      intro hd
      have hdt : d ≤ t := by omega
      have hIH := ih hdt
      rcases hwit (t - d - 1) (by omega) with h | h
      · exact h
      · have h2 : 2 * (t - d - 1) + 1 + 1 = 2 * (t - d) := by omega
        have h3 : 2 * (t - d - 1) + 1 + 1 < L := by
          have h4 := hPL (2 * (t - d)) hIH
          omega
        have h5 := hind (2 * (t - d - 1) + 1) h h3
        have h6 : 2 * (t - d) ∉ P := by rw [← h2]; exact h5
        exact absurd hIH h6
  intro e heL hee
  have hj : e / 2 ≤ t := by omega
  have hdowne := hdown (t - e / 2) (by omega)
  have h5 : 2 * (t - (t - e / 2)) = e := by omega
  rw [h5] at hdowne
  exact hdowne

/-! ## Chain-level independence and forcing -/

lemma ch_elem {N u m : ℕ} (hm : m ∈ ch N u) :
    ∃ e, e < Nat.log 2 (N / u) + 1 ∧ m = u * 2 ^ e := by
  unfold ch at hm
  rw [Finset.mem_image] at hm
  obtain ⟨e, he, hex⟩ := hm
  refine ⟨e, by have := Finset.mem_range.1 he; omega, ?_⟩
  exact hex.symm

lemma ch_elem_pos {N u m : ℕ} (hu : u ≠ 0) (hu2 : ¬ 2 ∣ u) (hm : m ∈ ch N u) :
    m = u * 2 ^ dv m := by
  obtain ⟨e, he, hex⟩ := ch_elem hm
  have h1 : dv m = e := by rw [hex]; exact dv_ch hu hu2
  rw [h1, hex]

lemma ch_elem_le {N u m : ℕ} (hu : 0 < u) (huN : u ≤ N) (hm : m ∈ ch N u) : m ≤ N := by
  obtain ⟨e, he, hex⟩ := ch_elem hm
  have hNu : N / u ≠ 0 := (div_pos_of_le hu huN).ne'
  have h1 : e ≤ Nat.log 2 (N / u) := by omega
  have h2 : 2 ^ e ≤ N / u := pow_le_of_log2_le hNu h1
  have h3 : u * 2 ^ e ≤ N := mul_le_of_div_le hu h2
  rw [hex]
  exact h3

lemma pos_inj_on_chain {N u : ℕ} (hu : u ≠ 0) (hu2 : ¬ 2 ∣ u) (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ∈ ch N u) :
    ∀ m₁ ∈ S, ∀ m₂ ∈ S, dv m₁ = dv m₂ → m₁ = m₂ := by
  intro m₁ h₁ m₂ h₂ heq
  rw [ch_elem_pos hu hu2 (hS m₁ h₁), ch_elem_pos hu hu2 (hS m₂ h₂), heq]

lemma chain_bound {N u : ℕ} (hu : 0 < u) (hu2 : ¬ 2 ∣ u) (huN : u ≤ N)
    (S : Finset ℕ) (hS : S ⊆ ch N u)
    (hind : ∀ m ∈ S, 2 * m ≤ N → 2 * m ∉ S) :
    S.card ≤ (Nat.log 2 (N / u) + 2) / 2 := by
  classical
  set L := Nat.log 2 (N / u) + 1 with hL
  set P := S.image (fun m => dv m) with hP
  have hcardP : P.card = S.card := by
    rw [hP]
    exact Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact pos_inj_on_chain hu.ne' hu2 S (fun m hm => hS hm) a ha b hb hab)
  have hPL : ∀ e ∈ P, e < L := by
    intro e he
    rw [hP] at he
    obtain ⟨m, hm, hex⟩ := Finset.mem_image.1 he
    have h1 : dv m = e := hex
    have h2 : m ∈ ch N u := hS hm
    have h3 : m ≤ N := ch_elem_le hu huN h2
    have h4 : u * 2 ^ dv m ≤ N := by
      rw [← ch_elem_pos hu.ne' hu2 h2]
      omega
    have h5 : 2 ^ dv m ≤ N / u := div_le_of_mul_le hu h4
    have h6 : dv m ≤ Nat.log 2 (N / u) := log2_le_of_pow_le h5
    omega
  have hindP : ∀ e ∈ P, e + 1 < L → e + 1 ∉ P := by
    intro e he he1 hcon
    rw [hP] at he hcon
    obtain ⟨m, hm, hex⟩ := Finset.mem_image.1 he
    have h1 : dv m = e := hex
    obtain ⟨m', hm', hex'⟩ := Finset.mem_image.1 hcon
    have h2 : dv m' = e + 1 := hex'
    have hm2 : m ∈ ch N u := hS hm
    have hm2' : m' ∈ ch N u := hS hm'
    have h3 : m = u * 2 ^ e := by rw [ch_elem_pos hu.ne' hu2 hm2, h1]
    have h4 : m' = u * 2 ^ (e + 1) := by rw [ch_elem_pos hu.ne' hu2 hm2', h2]
    have h5 : 2 * m = m' := by
      rw [h3, h4, Nat.pow_succ]
      ring
    have h6 : m' ≤ N := ch_elem_le hu huN hm2'
    have h7 : 2 * m ≤ N := by rw [h5]; exact h6
    have h8 : 2 * m ∉ S := hind m hm h7
    rw [h5] at h8
    exact h8 hm'
  have hbound := indep_bound P hPL hindP
  rw [hcardP] at hbound
  exact hbound

lemma chain_forcing {N u : ℕ} (hu : 0 < u) (hu2 : ¬ 2 ∣ u) (huN : u ≤ N)
    (S : Finset ℕ) (hS : S ⊆ ch N u)
    (hind : ∀ m ∈ S, 2 * m ≤ N → 2 * m ∉ S)
    (hLodd : Nat.log 2 (N / u) % 2 = 0)
    (hcard : (Nat.log 2 (N / u) + 2) / 2 ≤ S.card) :
    ∀ e, e < Nat.log 2 (N / u) + 1 → e % 2 = 0 → u * 2 ^ e ∈ S := by
  classical
  set L := Nat.log 2 (N / u) + 1 with hL
  set P := S.image (fun m => dv m) with hP
  have hcardP : P.card = S.card := by
    rw [hP]
    exact Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact pos_inj_on_chain hu.ne' hu2 S (fun m hm => hS hm) a ha b hb hab)
  have hPL : ∀ e ∈ P, e < L := by
    intro e he
    rw [hP] at he
    obtain ⟨m, hm, hex⟩ := Finset.mem_image.1 he
    have h1 : dv m = e := hex
    have h2 : m ∈ ch N u := hS hm
    have h3 : m ≤ N := ch_elem_le hu huN h2
    have h4 : u * 2 ^ dv m ≤ N := by
      rw [← ch_elem_pos hu.ne' hu2 h2]
      omega
    have h5 : 2 ^ dv m ≤ N / u := div_le_of_mul_le hu h4
    have h6 : dv m ≤ Nat.log 2 (N / u) := log2_le_of_pow_le h5
    omega
  have hindP : ∀ e ∈ P, e + 1 < L → e + 1 ∉ P := by
    intro e he he1 hcon
    rw [hP] at he hcon
    obtain ⟨m, hm, hex⟩ := Finset.mem_image.1 he
    have h1 : dv m = e := hex
    obtain ⟨m', hm', hex'⟩ := Finset.mem_image.1 hcon
    have h2 : dv m' = e + 1 := hex'
    have hm2 : m ∈ ch N u := hS hm
    have hm2' : m' ∈ ch N u := hS hm'
    have h3 : m = u * 2 ^ e := by rw [ch_elem_pos hu.ne' hu2 hm2, h1]
    have h4 : m' = u * 2 ^ (e + 1) := by rw [ch_elem_pos hu.ne' hu2 hm2', h2]
    have h5 : 2 * m = m' := by
      rw [h3, h4, Nat.pow_succ]
      ring
    have h6 : m' ≤ N := ch_elem_le hu huN hm2'
    have h7 : 2 * m ≤ N := by rw [h5]; exact h6
    have h8 : 2 * m ∉ S := hind m hm h7
    rw [h5] at h8
    exact h8 hm'
  have hLp : L % 2 = 1 := by omega
  have hcardP' : (L + 1) / 2 ≤ P.card := by
    rw [hcardP]
    omega
  have hforce := indep_forcing hLp P hPL hindP hcardP'
  intro e heL hee
  have hmem : e ∈ P := hforce e heL hee
  rw [hP] at hmem
  obtain ⟨m, hm, hex⟩ := Finset.mem_image.1 hmem
  have h1 : dv m = e := hex
  have h2 : m ∈ ch N u := hS hm
  have h3 : m = u * 2 ^ dv m := ch_elem_pos hu.ne' hu2 h2
  have h4 : u * 2 ^ e = m := by rw [h3, h1]
  rw [h4]
  exact hm

/-! ## Cast helpers (copied from the star file) -/

lemma cast_div_le (a k : ℕ) (hk : 0 < k) : ((a / k : ℕ) : ℝ) ≤ (a : ℝ) / k := by
  rw [le_div_iff₀ (by exact_mod_cast hk : (0:ℝ) < k)]
  calc ((a / k : ℕ) : ℝ) * k = ((a / k * k : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ (a : ℝ) := by exact_mod_cast Nat.div_mul_le_self a k

lemma cast_div_lt_mul_add (a k : ℕ) (hk : 0 < k) : (a : ℝ) < ((a / k : ℕ) : ℝ) * k + k := by
  have h2 : (a / k) * k + a % k = a := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod a k
  have h : ((a / k : ℕ) : ℝ) * k + ((a % k : ℕ) : ℝ) = (a : ℝ) := by
    exact_mod_cast h2
  have hmod : ((a % k : ℕ) : ℝ) < k := by exact_mod_cast Nat.mod_lt a hk
  linarith

/-! ## Counting even positions -/

lemma card_filter_even_range (L : ℕ) :
    ((Finset.range L).filter (fun e => e % 2 = 0)).card = (L + 1) / 2 := by
  classical
  have hinj : ∀ j ∈ Finset.range ((L + 1) / 2), 2 * j % 2 = 0 ∧ 2 * j < L := by
    intro j hj
    have h1 := Finset.mem_range.1 hj
    constructor
    · omega
    · omega
  have hsub : (Finset.range ((L + 1) / 2)).image (fun j => 2 * j) ⊆
      (Finset.range L).filter (fun e => e % 2 = 0) := by
    intro x hx
    obtain ⟨j, hj, hx2⟩ := Finset.mem_image.1 hx
    have h1 := hinj j hj
    have hx2' : 2 * j = x := hx2
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ?_⟩
    · have : x < L := by omega
      exact this
    · have : x % 2 = 0 := by omega
      exact this
  have hsurj : (Finset.range L).filter (fun e => e % 2 = 0) ⊆
      (Finset.range ((L + 1) / 2)).image (fun j => 2 * j) := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    have hxL : x < L := Finset.mem_range.1 h1
    have hxe : x % 2 = 0 := h2
    refine Finset.mem_image.2 ⟨x / 2, Finset.mem_range.2 ?_, ?_⟩
    · omega
    · omega
  have hcard1 := Finset.card_le_card hsub
  have hcard2 := Finset.card_le_card hsurj
  have hcard_img : ((Finset.range ((L + 1) / 2)).image (fun j => 2 * j)).card =
      (L + 1) / 2 := by
    have h1 := Finset.card_image_of_injOn
      (f := fun j => 2 * j) (s := Finset.range ((L + 1) / 2)) (by
        intro a _ b _ hab
        have h2 : 2 * a = 2 * b := hab
        omega)
    rw [h1, Finset.card_range]
  omega

/-! ## Even-position counting per chain -/

lemma ch_od {N u m : ℕ} (hu : u ≠ 0) (hu2 : ¬ 2 ∣ u) (hm : m ∈ ch N u) : od m = u := by
  obtain ⟨e, he, hex⟩ := ch_elem hm
  have h1 : dv m = e := by rw [hex]; exact dv_ch hu hu2
  have h2 : od m = m / 2 ^ e := by unfold od; rw [h1]
  rw [h2, hex, Nat.mul_comm]
  exact Nat.mul_div_cancel_left u (Nat.two_pow_pos e)

lemma ch_filter_even_card {N u : ℕ} (hu : 0 < u) (hu2 : ¬ 2 ∣ u) (huN : u ≤ N) :
    ((ch N u).filter (fun m => dv m % 2 = 0)).card = (Nat.log 2 (N / u) + 2) / 2 := by
  classical
  set L := Nat.log 2 (N / u) + 1 with hL
  set S := (ch N u).filter (fun m => dv m % 2 = 0) with hS
  set P := S.image (fun m => dv m) with hP
  have hcardP : P.card = S.card := by
    rw [hP]
    exact Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact pos_inj_on_chain hu.ne' hu2 S (fun m hm =>
        Finset.mem_filter.1 hm |>.1) a ha b hb hab)
  have hsub1 : P ⊆ (Finset.range L).filter (fun e => e % 2 = 0) := by
    intro e he
    rw [hP] at he
    obtain ⟨m, hm, hex⟩ := Finset.mem_image.1 he
    have h1 : dv m = e := hex
    have hme : dv m % 2 = 0 := (Finset.mem_filter.1 hm).2
    have hm2 : m ∈ ch N u := (Finset.mem_filter.1 hm).1
    have h3 : m ≤ N := ch_elem_le hu huN hm2
    have h4 : u * 2 ^ dv m ≤ N := by
      rw [← ch_elem_pos hu.ne' hu2 hm2]
      omega
    have h5 : 2 ^ dv m ≤ N / u := div_le_of_mul_le hu h4
    have h6 : dv m ≤ Nat.log 2 (N / u) := log2_le_of_pow_le h5
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), by rw [← h1]; exact hme⟩
  have hsub2 : (Finset.range L).filter (fun e => e % 2 = 0) ⊆ P := by
    intro e he
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 he
    have heL : e < L := Finset.mem_range.1 h1
    have hee : e % 2 = 0 := h2
    have hmem : u * 2 ^ e ∈ ch N u := (mem_ch hu huN).2 (by
      have hNu : N / u ≠ 0 := (div_pos_of_le hu huN).ne'
      have hq : 2 ^ e ≤ N / u := pow_le_of_log2_le hNu (by omega)
      exact mul_le_of_div_le hu hq)
    have hdv : dv (u * 2 ^ e) = e := dv_ch hu.ne' hu2
    refine Finset.mem_image.2 ⟨u * 2 ^ e, ?_, ?_⟩
    · rw [hS]
      exact Finset.mem_filter.2 ⟨hmem, by rw [hdv]; exact hee⟩
    · rw [hdv]
  have hcard_evens := card_filter_even_range L
  have h1 : P.card = ((Finset.range L).filter (fun e => e % 2 = 0)).card := by
    exact le_antisymm (Finset.card_le_card hsub1) (Finset.card_le_card hsub2)
  omega

/-! ## Fiber partitions and the deficit bound -/

lemma idx_props {N u : ℕ} (hu : u ∈ (Finset.Icc 1 N).image od) :
    0 < u ∧ ¬ 2 ∣ u ∧ u ≤ N := by
  obtain ⟨m, hm, hex⟩ := Finset.mem_image.1 hu
  have h1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
  have h2 : m ≤ N := (Finset.mem_Icc.1 hm).2
  have hm0 : m ≠ 0 := by omega
  have h3 : od m = u := hex
  have h4 : 0 < od m := od_pos hm0
  have h5 : ¬ 2 ∣ od m := od_not_two_dvd hm0
  have h6 : od m ≤ m := od_le m
  omega

/-- The deficit bound: the number of deficient chains plus `|B|` is at most
the number of even-valuation elements. -/
lemma bad_le_deficit {N : ℕ} (B : Finset ℕ) (hB : B ⊆ Finset.Icc 1 N)
    (hind : ∀ m ∈ B, 2 * m ≤ N → 2 * m ∉ B) :
    (((Finset.Icc 1 N).image od).filter (fun u =>
        (B.filter (fun m => od m = u)).card < (Nat.log 2 (N / u) + 2) / 2)).card + B.card ≤
      ((Finset.Icc 1 N).filter (fun m => dv m % 2 = 0)).card := by
  classical
  set idx := (Finset.Icc 1 N).image od with hidx
  set bad := idx.filter (fun u =>
        (B.filter (fun m => od m = u)).card < (Nat.log 2 (N / u) + 2) / 2) with hbad
  set Ev := (Finset.Icc 1 N).filter (fun m => dv m % 2 = 0) with hEv
  have hup : ∀ u ∈ idx, 0 < u ∧ ¬ 2 ∣ u ∧ u ≤ N := fun u hu => idx_props hu
  have hBsub : ∀ u ∈ idx, ∀ m ∈ B.filter (fun m => od m = u), m ∈ ch N u := by
    intro u hu m hm
    obtain ⟨hmb, hmod⟩ := Finset.mem_filter.1 hm
    have h1 : 1 ≤ m := (Finset.mem_Icc.1 (hB hmb)).1
    have h2 : m ≤ N := (Finset.mem_Icc.1 (hB hmb)).2
    have hgoal : m ∈ ch N (od m) := mem_ch_of_mem_Icc h1 h2
    rw [hmod] at hgoal
    exact hgoal
  have hBbound : ∀ u ∈ idx,
      (B.filter (fun m => od m = u)).card ≤ (Nat.log 2 (N / u) + 2) / 2 := by
    intro u hu
    obtain ⟨hu1, hu2, hu3⟩ := hup u hu
    exact chain_bound hu1 hu2 hu3 _ (fun m hm => hBsub u hu m hm)
      (fun m hm h2m hcon => hind m (Finset.mem_filter.1 hm).1 h2m
        (Finset.mem_filter.1 hcon).1)
  have hEfib : ∀ u ∈ idx,
      (Ev.filter (fun m => od m = u)).card = (Nat.log 2 (N / u) + 2) / 2 := by
    intro u hu
    obtain ⟨hu1, hu2, hu3⟩ := hup u hu
    have hset : Ev.filter (fun m => od m = u) = (ch N u).filter (fun m => dv m % 2 = 0) := by
      ext m
      constructor
      · intro hm
        obtain ⟨hm', hmod⟩ := Finset.mem_filter.1 hm
        obtain ⟨hm1, hme⟩ := Finset.mem_filter.1 hm'
        have h1 : 1 ≤ m := (Finset.mem_Icc.1 hm1).1
        have h2 : m ≤ N := (Finset.mem_Icc.1 hm1).2
        have hgoal : m ∈ ch N (od m) := mem_ch_of_mem_Icc h1 h2
        rw [hmod] at hgoal
        exact Finset.mem_filter.2 ⟨hgoal, hme⟩
      · intro hm
        obtain ⟨hch, hme⟩ := Finset.mem_filter.1 hm
        have hmN : m ≤ N := ch_elem_le hu1 hu3 hch
        have hmod : od m = u := ch_od hu1.ne' hu2 hch
        obtain ⟨e, he, hex⟩ := ch_elem hch
        have hm1 : 1 ≤ m := by
          have : u * 2 ^ e ≥ u := Nat.le_mul_of_pos_right u (Nat.two_pow_pos e)
          omega
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hm1, hmN⟩, hme⟩, hmod⟩
    rw [hset]
    exact ch_filter_even_card hu1 hu2 hu3
  have hBpart : ∑ u ∈ idx, (B.filter (fun m => od m = u)).card = B.card := by
    have hmaps : Set.MapsTo od ↑B ↑idx := by
      intro m hm
      simp only [Finset.mem_coe]
      exact Finset.mem_image.2 ⟨m, hB hm, rfl⟩
    exact (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hEpart : ∑ u ∈ idx, (Ev.filter (fun m => od m = u)).card = Ev.card := by
    have hmaps : Set.MapsTo od ↑Ev ↑idx := by
      intro m hm
      simp only [Finset.mem_coe]
      obtain ⟨hm1, -⟩ := Finset.mem_filter.1 hm
      exact Finset.mem_image.2 ⟨m, hm1, rfl⟩
    exact (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hbadcon : ∀ u ∈ idx,
      (if u ∈ bad then 1 else 0) + (B.filter (fun m => od m = u)).card ≤
      (Ev.filter (fun m => od m = u)).card := by
    intro u hu
    by_cases hcon : u ∈ bad
    · rw [if_pos hcon]
      rw [hbad] at hcon
      have h1 := (Finset.mem_filter.1 hcon).2
      have h2 := hEfib u hu
      omega
    · rw [if_neg hcon]
      have h1 := hBbound u hu
      have h2 := hEfib u hu
      omega
  have hsum : ∑ u ∈ idx, ((if u ∈ bad then 1 else 0) +
      (B.filter (fun m => od m = u)).card) ≤
      ∑ u ∈ idx, (Ev.filter (fun m => od m = u)).card :=
    Finset.sum_le_sum hbadcon
  have hLHS : ∑ u ∈ idx, ((if u ∈ bad then 1 else 0) +
      (B.filter (fun m => od m = u)).card) = bad.card + B.card := by
    have h1 : ∑ u ∈ idx, ((if u ∈ bad then 1 else 0) +
        (B.filter (fun m => od m = u)).card) =
        ∑ u ∈ idx, (if u ∈ bad then 1 else 0) +
        ∑ u ∈ idx, (B.filter (fun m => od m = u)).card := by
      rw [Finset.sum_add_distrib]
    have hsub : idx.filter (fun u => u ∈ bad) = bad := by
      ext u
      constructor
      · intro h
        exact (Finset.mem_filter.1 h).2
      · intro h
        rw [hbad] at h
        exact Finset.mem_filter.2 ⟨Finset.mem_filter.1 h |>.1, h⟩
    have h2 : ∑ u ∈ idx, (if u ∈ bad then 1 else 0) = bad.card := by
      rw [← Finset.sum_filter, hsub]
      simp
    rw [h1, h2, hBpart]
  rw [hLHS] at hsum
  rw [hEpart] at hsum
  exact hsum

/-! ## The E-bound: even-valuation elements are at most `(2/3)N + log N + 2` -/

lemma geom_quarter (n : ℕ) :
    ∑ j ∈ Finset.range n, ((1:ℝ)/4)^j = (4:ℝ)/3 * (1 - ((1:ℝ)/4)^n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : ((1:ℝ)/4)^(n+1) = ((1:ℝ)/4)^n / 4 := by
      rw [pow_succ]; field_simp
    rw [h1]
    field_simp
    ring

lemma odds_le (M : ℕ) : ((Finset.Icc 1 M).filter (fun u => ¬ 2 ∣ u)).card ≤ M / 2 + 1 := by
  classical
  have hsub : (Finset.Icc 1 M).filter (fun u => ¬ 2 ∣ u) ⊆
      (Finset.range ((M+1)/2)).image (fun t => 2*t+1) := by
    intro u hu
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hu
    have hu1 : 1 ≤ u := (Finset.mem_Icc.1 h1).1
    have huM : u ≤ M := (Finset.mem_Icc.1 h1).2
    have hu2 : ¬ 2 ∣ u := h2
    refine Finset.mem_image.2 ⟨u/2, Finset.mem_range.2 ?_, ?_⟩
    · omega
    · have h3 : 2*(u/2)+1 = u := by omega
      exact h3
  have hcard_img := Finset.card_le_card hsub
  have hcard_img2 : ((Finset.range ((M+1)/2)).image (fun t => 2*t+1)).card ≤ (M+1)/2 := by
    have h1 := Finset.card_image_of_injOn (f := fun t => 2*t+1)
      (s := Finset.range ((M+1)/2)) (by
        intro a _ b _ hab
        have h2 : 2*a+1 = 2*b+1 := hab
        omega)
    rw [h1, Finset.card_range]
  omega

/-- The key level bound: `#{m ∈ [1,N] : v₂ m = 2j} ≤ N / 2^{2j+1} + 1`. -/
lemma level_le {N j : ℕ} :
    ((Finset.Icc 1 N).filter (fun m => dv m = 2*j)).card ≤ N / 2^(2*j+1) + 1 := by
  classical
  set q := 2^(2*j) with hq
  have hqpos : 0 < q := Nat.two_pow_pos _
  have hq2 : 2 * q = 2^(2*j+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hsub : ((Finset.Icc 1 N).filter (fun m => dv m = 2*j)).image (fun m => m / q) ⊆
      (Finset.Icc 1 (N / q)).filter (fun u => ¬ 2 ∣ u) := by
    intro x hx
    obtain ⟨m, hm, hx2⟩ := Finset.mem_image.1 hx
    obtain ⟨hmI, hmdv⟩ := Finset.mem_filter.1 hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hmI).1
    have hmN : m ≤ N := (Finset.mem_Icc.1 hmI).2
    have hm0 : m ≠ 0 := by omega
    have hx2' : m / q = x := hx2
    have hod : od m = m / 2 ^ (2*j) := by unfold od; rw [hmdv]
    have hqx : m / 2^(2*j) = x := by rw [← hq, ← hx2']
    have hodd : ¬ 2 ∣ m / 2^(2*j) := by
      have h1 := od_not_two_dvd hm0
      rw [hod] at h1
      exact h1
    have hpos : 1 ≤ m / 2^(2*j) := by
      have h1 := od_pos hm0
      rw [hod] at h1
      exact h1
    have hle : m / 2^(2*j) ≤ N / 2^(2*j) := Nat.div_le_div_right hmN
    rw [← hqx]
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hpos, hle⟩, hodd⟩
  have hinj : ∀ m₁ ∈ (Finset.Icc 1 N).filter (fun m => dv m = 2*j),
      ∀ m₂ ∈ (Finset.Icc 1 N).filter (fun m => dv m = 2*j),
      m₁ / q = m₂ / q → m₁ = m₂ := by
    intro m₁ hm₁ m₂ hm₂ heq
    obtain ⟨hmI₁, hmdv₁⟩ := Finset.mem_filter.1 hm₁
    obtain ⟨hmI₂, hmdv₂⟩ := Finset.mem_filter.1 hm₂
    have hdvd₁ : q ∣ m₁ := by rw [hq, ← hmdv₁]; exact dv_dvd m₁
    have hdvd₂ : q ∣ m₂ := by rw [hq, ← hmdv₂]; exact dv_dvd m₂
    have h1 : m₁ / q * q = m₁ := Nat.div_mul_cancel hdvd₁
    have h2 : m₂ / q * q = m₂ := Nat.div_mul_cancel hdvd₂
    rw [← h1, heq, h2]
  have hcard_img : (((Finset.Icc 1 N).filter (fun m => dv m = 2*j)).image
      (fun m => m / q)).card = ((Finset.Icc 1 N).filter (fun m => dv m = 2*j)).card :=
    Finset.card_image_of_injOn (by
      intro a ha b hb hab
      exact hinj a ha b hb hab)
  have hle1 := Finset.card_le_card hsub
  have hle2 := odds_le (N / q)
  have hfin : (N / q) / 2 + 1 ≤ N / 2^(2*j+1) + 1 := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm, hq2]
  omega

/-- The E-bound: `#{m ∈ [1,N] : v₂ m even} ≤ (2/3)N + log₂ N + 2`. -/
lemma ebound {N : ℕ} (hN : 1 ≤ N) :
    (((Finset.Icc 1 N).filter (fun m => dv m % 2 = 0)).card : ℝ) ≤
      (2:ℝ)/3 * N + (Nat.log 2 N : ℝ) + 2 := by
  classical
  set J := Nat.log 2 N with hJ
  set E := (Finset.Icc 1 N).filter (fun m => dv m % 2 = 0) with hE
  have hdvle : ∀ m ∈ E, dv m ≤ J := by
    intro m hm
    obtain ⟨hmI, -⟩ := Finset.mem_filter.1 hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hmI).1
    have hmN : m ≤ N := (Finset.mem_Icc.1 hmI).2
    have h1 : (2:ℕ)^(dv m) ≤ m := Nat.le_of_dvd (by omega) (dv_dvd m)
    have h2 : dv m ≤ Nat.log 2 m := log2_le_of_pow_le h1
    have h3 : Nat.log 2 m ≤ Nat.log 2 N := Nat.log_mono_right hmN
    omega
  have hmaps : Set.MapsTo (fun m => dv m / 2) ↑E ↑(Finset.range (J + 1)) := by
    intro m hm
    simp only [Finset.mem_coe]
    exact Finset.mem_range.2 (by
      have := hdvle m hm
      omega)
  have hcard : E.card = ∑ j ∈ Finset.range (J + 1),
      (E.filter (fun m => dv m / 2 = j)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ j ∈ Finset.range (J + 1),
      (E.filter (fun m => dv m / 2 = j)).card ≤ N / 2^(2*j+1) + 1 := by
    intro j hj
    have hsub : E.filter (fun m => dv m / 2 = j) ⊆
        (Finset.Icc 1 N).filter (fun m => dv m = 2*j) := by
      intro m hm
      obtain ⟨hmE, hmq⟩ := Finset.mem_filter.1 hm
      obtain ⟨hmI, hme⟩ := Finset.mem_filter.1 hmE
      refine Finset.mem_filter.2 ⟨hmI, ?_⟩
      have h1 : dv m % 2 = 0 := hme
      have h2 : dv m / 2 = j := hmq
      omega
    have h1 := Finset.card_le_card hsub
    have h2 := level_le (N := N) (j := j)
    omega
  -- cast the partition to ℝ
  have hcardR : (E.card : ℝ) = ∑ j ∈ Finset.range (J + 1),
      ((E.filter (fun m => dv m / 2 = j)).card : ℝ) := by
    exact_mod_cast hcard
  have hsum : ∑ j ∈ Finset.range (J + 1),
      ((E.filter (fun m => dv m / 2 = j)).card : ℝ) ≤
      ∑ j ∈ Finset.range (J + 1), (((N / 2^(2*j+1) : ℕ) : ℝ) + 1) := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    have h1 := hfib j hj
    have h1R : ((E.filter (fun m => dv m / 2 = j)).card : ℝ) ≤
        ((N / 2 ^ (2 * j + 1) : ℕ) : ℝ) + 1 := by exact_mod_cast h1
    have h2 : ((N / 2^(2*j+1) : ℕ) : ℝ) ≤ (N:ℝ) / (2:ℝ)^(2*j+1) := by
      simpa [Nat.cast_pow] using
        (cast_div_le N (2 ^ (2 * j + 1)) (Nat.two_pow_pos _))
    linarith
  have hsplit : ∑ j ∈ Finset.range (J + 1), (((N / 2^(2*j+1) : ℕ) : ℝ) + 1) ≤
      ∑ j ∈ Finset.range (J + 1), ((N:ℝ) / 2^(2*j+1)) + (J + 1) := by
    have h1 : ∑ j ∈ Finset.range (J + 1), (((N / 2^(2*j+1) : ℕ) : ℝ) + 1) =
        ∑ j ∈ Finset.range (J + 1), ((N / 2^(2*j+1) : ℕ) : ℝ) +
        ∑ j ∈ Finset.range (J + 1), (1:ℝ) := by
      rw [Finset.sum_add_distrib]
    have h2 : ∑ j ∈ Finset.range (J + 1), (1:ℝ) = J + 1 := by
      simp
    have h3 : ∑ j ∈ Finset.range (J + 1), ((N / 2^(2*j+1) : ℕ) : ℝ) ≤
        ∑ j ∈ Finset.range (J + 1), ((N:ℝ) / 2^(2*j+1)) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      simpa [Nat.cast_pow] using
        (cast_div_le N (2 ^ (2 * j + 1)) (Nat.two_pow_pos _))
    linarith
  have hp : ∀ j, ((2:ℕ)^(2*j+1) : ℝ) = 2 * (4:ℝ)^j := by
    intro j
    push_cast
    rw [pow_succ, pow_mul]
    norm_num
    ring
  have hcon : ∀ j ∈ Finset.range (J + 1),
      ((N:ℝ) / ((2:ℕ)^(2*j+1) : ℝ)) = (N:ℝ)/2 * ((1:ℝ)/4)^j := by
    intro j _
    rw [hp j]
    have h4 : (4 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    have hpow : ((1 : ℝ) / 4) ^ j = 1 / (4 : ℝ) ^ j := by
      rw [div_pow]
      norm_num
    rw [hpow]
    field_simp [h4]
  have hsum2 : ∑ j ∈ Finset.range (J + 1), ((N:ℝ) / ((2:ℕ)^(2*j+1) : ℝ)) =
      (N:ℝ)/2 * ∑ j ∈ Finset.range (J + 1), ((1:ℝ)/4)^j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    exact hcon j hj
  have hkey : (N:ℝ)/2 * ∑ j ∈ Finset.range (J + 1), ((1:ℝ)/4)^j ≤ (2:ℝ)/3 * N := by
    have hgeom := geom_quarter (J + 1)
    rw [hgeom]
    have h1 : (0:ℝ) ≤ ((1:ℝ)/4)^(J+1) := le_of_lt (pow_pos (by norm_num) (J+1))
    have h2 : (N:ℝ)/2 * ((4:ℝ)/3 * (1 - ((1:ℝ)/4)^(J+1))) =
        (2:ℝ)/3 * N * (1 - ((1:ℝ)/4)^(J+1)) := by
      field_simp
      ring
    have h3 : (0:ℝ) ≤ (2:ℝ)/3 * N * ((1:ℝ)/4)^(J+1) :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) h1
    rw [h2]
    have h4 : (2:ℝ)/3 * N * (1 - ((1:ℝ)/4)^(J+1)) = (2:ℝ)/3 * N -
        (2:ℝ)/3 * N * ((1:ℝ)/4)^(J+1) := by ring
    rw [h4]
    linarith
  have hfinal : (E.card : ℝ) ≤ (2:ℝ)/3 * N + ((J:ℕ):ℝ) + 2 := by
    have c1 := hcardR
    have c2 := hsum
    have c3 := hsplit
    have c4 := hsum2
    have c5 := hkey
    linarith
  exact hfinal

end Chn

open Finset Filter


namespace Star

/-! ### Cast helpers for natural division -/

lemma cast_div_le (a k : ℕ) (hk : 0 < k) : ((a / k : ℕ) : ℝ) ≤ (a : ℝ) / k := by
  rw [le_div_iff₀ (by exact_mod_cast hk : (0:ℝ) < k)]
  calc ((a / k : ℕ) : ℝ) * k = ((a / k * k : ℕ) : ℝ) := by
        push_cast; ring
    _ ≤ (a : ℝ) := by exact_mod_cast Nat.div_mul_le_self a k

lemma cast_div_lt_mul_add (a k : ℕ) (hk : 0 < k) : (a : ℝ) < ((a / k : ℕ) : ℝ) * k + k := by
  have h2 : (a / k) * k + a % k = a := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod a k
  have h : ((a / k : ℕ) : ℝ) * k + ((a % k : ℕ) : ℝ) = (a : ℝ) := by
    exact_mod_cast h2
  have hmod : ((a % k : ℕ) : ℝ) < k := by exact_mod_cast Nat.mod_lt a hk
  linarith

lemma cast_div_gt_sub_one (a k : ℕ) (hk : 0 < k) : (a : ℝ) / k - 1 < ((a / k : ℕ) : ℝ) := by
  have hk' : (0:ℝ) < k := by exact_mod_cast hk
  have h := cast_div_lt_mul_add a k hk
  have h2 : (a : ℝ) / k < ((a / k : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hk']
    have h3 : (((a / k : ℕ) : ℝ) + 1) * k = ((a / k : ℕ) : ℝ) * k + k := by ring
    linarith
  linarith

/-! ### Grids -/

/-- Roth threshold for density `δ/2` (parameter of `roth_3ap_theorem_nat`). -/
noncomputable def mB (δ : ℝ) : ℕ := cornersTheoremBound (δ / 6)

lemma mB_pos (δ : ℝ) : 1 ≤ mB δ := by
  unfold mB cornersTheoremBound
  omega

/-- The grid of residue `r ∈ [1, d]` in `[1, N]`: the set `{r + j * d | j < (N-r)/d + 1}`. -/
def grid (N d r : ℕ) : Finset ℕ :=
  (Finset.range ((N - r) / d + 1)).image (fun j => r + j * d)

/-- Residue representative in `[1, d]`. -/
def res (d x : ℕ) : ℕ := (x - 1) % d + 1

lemma res_le (d x : ℕ) (hd : 1 ≤ d) : 1 ≤ res d x ∧ res d x ≤ d := by
  have h1 : (x - 1) % d < d := Nat.mod_lt (x - 1) hd
  unfold res
  omega

lemma mem_grid {N d r x : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ d) (hd1 : 1 ≤ d) (hrN : r ≤ N) :
    x ∈ grid N d r ↔ x ∈ Finset.Icc 1 N ∧ (x - 1) % d = (r - 1) % d := by
  constructor
  · intro hx
    simp only [grid, mem_image, mem_range] at hx
    obtain ⟨j, hj, hxj⟩ := hx
    have hjd : j * d ≤ (N - r) / d * d := Nat.mul_le_mul_right d (Nat.le_of_lt_succ hj)
    have hjd2 : (N - r) / d * d ≤ N - r := Nat.div_mul_le_self _ _
    have hxr : j * d ≤ N - r := Nat.le_trans hjd hjd2
    have hx1 : x = r + j * d := by omega
    refine ⟨Finset.mem_Icc.2 ⟨by omega, ?_⟩, ?_⟩
    · omega
    · have hsplit : x - 1 = (r - 1) + j * d := by omega
      rw [hsplit, Nat.add_mul_mod_self_right]
  · rintro ⟨hx, hxmod⟩
    simp only [Finset.mem_Icc] at hx
    obtain ⟨hx1, hxN⟩ := hx
    have hd0 : 0 < d := hd1
    have hq : (x / d) * d + x % d = x := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod x d
    have hs_lt : x % d < d := Nat.mod_lt x hd0
    rcases Nat.eq_zero_or_pos (x % d) with hs0 | hs0
    · -- x % d = 0: x is a multiple of d; then r = d
      have hxd : (x / d) * d = x := by omega
      have hqpos : 1 ≤ x / d := by
        by_contra hcon
        have h0 : x / d = 0 := Nat.lt_one_iff.1 (Nat.not_le.1 hcon)
        rw [h0, Nat.zero_mul] at hxd
        omega
      have hge : d ≤ x := by rw [← hxd]; exact Nat.le_mul_of_pos_left d hqpos
      have hmodx1 : (x - 1) % d = d - 1 := by
        have hsplit : x - 1 = (d - 1) + (x / d - 1) * d := by
          have hexp : (x / d - 1) * d = (x / d) * d - d := by rw [Nat.sub_mul, Nat.one_mul]
          rw [hexp, hxd]
          omega
        rw [hsplit, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      have hr_eq : r = d := by
        have h1 : (r - 1) % d = d - 1 := by rw [← hxmod]; exact hmodx1
        have h2 : r - 1 < d := by omega
        rw [Nat.mod_eq_of_lt h2] at h1
        omega
      simp only [grid, mem_image, mem_range]
      refine ⟨x / d - 1, ?_, ?_⟩
      · show x / d - 1 < (N - r) / d + 1
        rw [hr_eq]
        have hexp : (x / d - 1) * d = (x / d) * d - d := by rw [Nat.sub_mul, Nat.one_mul]
        have hmul : (x / d - 1) * d ≤ N - d := by omega
        exact Nat.lt_succ_of_le (Nat.le_div_iff_mul_le hd0 |>.2 hmul)
      · show r + (x / d - 1) * d = x
        rw [hr_eq]
        have hexp : (x / d - 1) * d = (x / d) * d - d := by rw [Nat.sub_mul, Nat.one_mul]
        omega
    · -- x % d ≥ 1: then r = x % d
      have hmodx1 : (x - 1) % d = x % d - 1 := by
        have hsplit : x - 1 = (x % d - 1) + (x / d) * d := by omega
        rw [hsplit, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      have hr_eq : r = x % d := by
        have h1 : (r - 1) % d = x % d - 1 := by rw [← hxmod]; exact hmodx1
        have h2 : r - 1 < d := by omega
        rw [Nat.mod_eq_of_lt h2] at h1
        omega
      simp only [grid, mem_image, mem_range]
      refine ⟨x / d, ?_, ?_⟩
      · show x / d < (N - r) / d + 1
        rw [hr_eq]
        have hmul : (x / d) * d ≤ N - x % d := by omega
        exact Nat.lt_succ_of_le (Nat.le_div_iff_mul_le hd0 |>.2 hmul)
      · show r + (x / d) * d = x
        rw [hr_eq]
        omega

lemma card_grid (N d r : ℕ) (hd : 1 ≤ d) : (grid N d r).card = (N - r) / d + 1 := by
  have hinj : Set.InjOn (fun j => r + j * d) ↑(Finset.range ((N - r) / d + 1)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, mem_range] at ha hb
    dsimp only at hab
    have this : a * d = b * d := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < d) this
  rw [grid, Finset.card_image_of_injOn hinj, Finset.card_range]


/-- Pairs of distinct elements of `C` whose midpoint lies in `C`. -/
def pairSet (C : Finset ℕ) : Finset (ℕ × ℕ) :=
  (C ×ˢ C).filter (fun p => p.1 ≠ p.2 ∧ ∃ y ∈ C, p.1 + p.2 = 2 * y)

lemma mem_pairSet {C : Finset ℕ} {p : ℕ × ℕ} :
    p ∈ pairSet C ↔ p.1 ∈ C ∧ p.2 ∈ C ∧ p.1 ≠ p.2 ∧ ∃ y ∈ C, p.1 + p.2 = 2 * y := by
  constructor
  · intro h
    simp only [pairSet, mem_filter] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hm := mem_product.1 h1
    exact ⟨hm.1, hm.2, h2, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩
    simp only [pairSet, mem_filter]
    exact ⟨mem_product.2 ⟨h1, h2⟩, h3, h4⟩

lemma res_eq {d r : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ d) (x : ℕ) :
    res d x = r ↔ (x - 1) % d = (r - 1) % d := by
  have h1 : r - 1 < d := by omega
  unfold res
  rw [Nat.mod_eq_of_lt h1]
  omega

lemma grid_eq_filter {N d r : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ d) (hd1 : 1 ≤ d) (hrN : r ≤ N) :
    grid N d r = (Finset.Icc 1 N).filter (fun x => res d x = r) := by
  ext x
  rw [mem_filter, mem_grid hr1 hrd hd1 hrN, res_eq hr1 hrd]

lemma sum_inter_grid {N d : ℕ} (hd1 : 1 ≤ d) (hdN : d ≤ N) (C : Finset ℕ)
    (hC : C ⊆ Finset.Icc 1 N) :
    ∑ r ∈ Finset.Icc 1 d, (C ∩ grid N d r).card = C.card := by
  classical
  have hmap : Set.MapsTo (res d) ↑C ↑(Finset.Icc 1 d) := by
    intro x hx
    simp only [Finset.mem_coe]
    have hx' := hC hx
    have hle := res_le d x hd1
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega
  have hcard : C.card = ∑ r ∈ Finset.Icc 1 d, (C.filter (fun x => res d x = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  rw [hcard]
  refine Finset.sum_congr rfl ?_
  intro r hr
  have hr1 : 1 ≤ r := (Finset.mem_Icc.1 hr).1
  have hrd : r ≤ d := (Finset.mem_Icc.1 hr).2
  have hrN : r ≤ N := Nat.le_trans hrd hdN
  have hfilter : C.filter (fun x => res d x = r) = C ∩ grid N d r := by
    ext x
    constructor
    · intro hx
      have hxc : x ∈ C := (mem_filter.1 hx).1
      have hres : res d x = r := (mem_filter.1 hx).2
      refine mem_inter.2 ⟨hxc, ?_⟩
      rw [mem_grid hr1 hrd hd1 hrN]
      exact ⟨hC hxc, (res_eq hr1 hrd x).1 hres⟩
    · intro hx
      obtain ⟨hxc, hxg⟩ := mem_inter.1 hx
      refine mem_filter.2 ⟨hxc, ?_⟩
      rw [res_eq hr1 hrd x]
      exact ((mem_grid hr1 hrd hd1 hrN).1 hxg).2
  rw [hfilter]

lemma sum_grid_N {N d : ℕ} (hd1 : 1 ≤ d) (hdN : d ≤ N) :
    ∑ r ∈ Finset.Icc 1 d, (grid N d r).card = N := by
  classical
  have hmap : Set.MapsTo (res d) ↑(Finset.Icc 1 N) ↑(Finset.Icc 1 d) := by
    intro x hx
    simp only [Finset.mem_coe] at hx
    have hle := res_le d x hd1
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega
  have hcard : (Finset.Icc 1 N).card =
      ∑ r ∈ Finset.Icc 1 d, ((Finset.Icc 1 N).filter (fun x => res d x = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  rw [hIcc] at hcard
  calc ∑ r ∈ Finset.Icc 1 d, (grid N d r).card
      = ∑ r ∈ Finset.Icc 1 d, ((Finset.Icc 1 N).filter (fun x => res d x = r)).card := by
        refine Finset.sum_congr rfl ?_
        intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.1 hr).1
        have hrd : r ≤ d := (Finset.mem_Icc.1 hr).2
        have hrN : r ≤ N := Nat.le_trans hrd hdN
        rw [grid_eq_filter hr1 hrd hd1 hrN]
    _ = N := hcard.symm

/-- Grid length is at least `mB δ` when `mB δ * d ≤ N`. -/
lemma grid_len_ge {δ : ℝ} {N d r : ℕ} (hr1 : 1 ≤ r) (hrd : r ≤ d) (hd0 : 0 < d)
    (hmd : mB δ * d ≤ N) : mB δ ≤ (N - r) / d + 1 := by
  have key : (mB δ - 1) * d ≤ N - r := by
    have h1 : (mB δ - 1) * d = mB δ * d - d := by
      rw [Nat.sub_mul, Nat.one_mul]
    have h2 : mB δ * d ≤ N := hmd
    have : d ≤ N := Nat.le_trans (Nat.le_mul_of_pos_left d (mB_pos δ)) hmd
    omega
  have := Nat.le_div_iff_mul_le hd0 |>.2 key
  omega

/-- Grid length is at most `2 * mB δ` when `d ≥ N / (2 * mB δ) + 1`. -/
lemma grid_len_le {δ : ℝ} {N d r : ℕ} (hd0 : 0 < d) (hr1 : 1 ≤ r)
    (hD1 : N / (2 * mB δ) + 1 ≤ d) : (N - r) / d + 1 ≤ 2 * mB δ := by
  have h1 : (2 * mB δ) * (N / (2 * mB δ)) + N % (2 * mB δ) = N :=
    Nat.div_add_mod N (2 * mB δ)
  have h2 : (2 * mB δ) * (N / (2 * mB δ)) + 2 * mB δ ≤ (2 * mB δ) * d := by
    have h := Nat.mul_le_mul_left (2 * mB δ) hD1
    rwa [Nat.mul_add, Nat.mul_one] at h
  have h3 : N % (2 * mB δ) < 2 * mB δ := Nat.mod_lt _ (by have := mB_pos δ; omega)
  have hlt : N < 2 * mB δ * d := by
    calc N = (2 * mB δ) * (N / (2 * mB δ)) + N % (2 * mB δ) := h1.symm
      _ < (2 * mB δ) * (N / (2 * mB δ)) + 2 * mB δ := by omega
      _ ≤ 2 * mB δ * d := h2
  have hdiv : (N - r) / d < 2 * mB δ := Nat.div_lt_iff_lt_mul hd0 |>.2 (by omega)
  omega


/-- A rich grid of `C` (density ≥ `δ/2` on the grid, grid length in `[mB δ, 2 * mB δ]`)
contains a pair of distinct elements of `C` whose midpoint is in `C`, whose span is
`t * d` with `1 ≤ t < 2 * mB δ`, and whose first coordinate has residue `r`. -/
lemma rich_grid_pair {N d r : ℕ} {δ : ℝ} {C : Finset ℕ} (hδ : 0 < δ)
    (hr1 : 1 ≤ r) (hrd : r ≤ d) (hd1 : 1 ≤ d) (hrN : r ≤ N)
    (hmd : mB δ * d ≤ N) (hD1 : N / (2 * mB δ) + 1 ≤ d)
    (hrich : (δ/2) * (((N - r) / d + 1 : ℕ) : ℝ) ≤ ((C ∩ grid N d r).card : ℝ)) :
    ∃ p : ℕ × ℕ, ∃ t : ℕ, p ∈ pairSet C ∧ 1 ≤ t ∧ t * d = p.2 - p.1 ∧
      (p.1 - 1) % d + 1 = r ∧ t < 2 * mB δ := by
  have hd0 : 0 < d := hd1
  have hmL : mB δ ≤ (N - r) / d + 1 := grid_len_ge hr1 hrd hd0 hmd
  have hLle : (N - r) / d + 1 ≤ 2 * mB δ := grid_len_le hd0 hr1 hD1
  have hinj : Set.InjOn (fun j => r + j * d)
      ↑((Finset.range ((N - r) / d + 1)).filter (fun j => r + j * d ∈ C)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, mem_filter] at ha hb
    dsimp only at hab
    have hae : a * d = b * d := by omega
    exact Nat.eq_of_mul_eq_mul_right (by omega) hae
  have himg : ((Finset.range ((N - r) / d + 1)).filter (fun j => r + j * d ∈ C)).image
      (fun j => r + j * d) = C ∩ grid N d r := by
    ext x
    constructor
    · intro hx
      simp only [mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      have hj' := mem_filter.1 hj
      refine mem_inter.2 ⟨hj'.2, ?_⟩
      simp only [grid, mem_image]
      exact ⟨j, hj'.1, rfl⟩
    · intro hx
      obtain ⟨hxC, hxg⟩ := mem_inter.1 hx
      simp only [grid, mem_image] at hxg
      obtain ⟨j, hj, rfl⟩ := hxg
      refine mem_image.2 ⟨j, mem_filter.2 ⟨hj, hxC⟩, rfl⟩
  have hbij : (C ∩ grid N d r).card =
      ((Finset.range ((N - r) / d + 1)).filter (fun j => r + j * d ∈ C)).card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  have hAε : (δ/2) * (((N - r) / d + 1 : ℕ) : ℝ) ≤
      (((Finset.range ((N - r) / d + 1)).filter (fun j => r + j * d ∈ C)).card : ℝ) := by
    rw [← hbij]
    exact hrich
  have hRoth := roth_3ap_theorem_nat (δ/2) (by positivity)
    (by rw [show ((δ:ℝ)/2)/3 = δ/6 from by ring]; exact hmL)
    ((Finset.range ((N - r) / d + 1)).filter (fun j => r + j * d ∈ C))
    (Finset.filter_subset _ _) hAε
  rw [threeAPFree_iff_eq_right] at hRoth
  push_neg at hRoth
  obtain ⟨ja, hja, jb, hjb, jc, hjc, hsum, hne⟩ := hRoth
  have hmema := mem_filter.1 (Finset.mem_coe.1 hja)
  have hmemb := mem_filter.1 (Finset.mem_coe.1 hjb)
  have hememc := mem_filter.1 (Finset.mem_coe.1 hjc)
  have hjaL := Finset.mem_range.1 hmema.1
  have hjbL := Finset.mem_range.1 hmemb.1
  have hjcL := Finset.mem_range.1 hememc.1
  rcases Nat.lt_or_ge ja jc with hlt | hge
  · refine ⟨(r + ja * d, r + jc * d), jc - ja, ?_, ?_, ?_, ?_, ?_⟩
    · refine mem_pairSet.2 ⟨hmema.2, hememc.2, ?_, ⟨r + jb * d, hmemb.2, ?_⟩⟩
      · intro hcon
        have hcancel : ja * d = jc * d := by omega
        have : ja = jc := Nat.eq_of_mul_eq_mul_right hd0 hcancel
        omega
      · have hmul : ja * d + jc * d = jb * d + jb * d := by
          rw [← Nat.add_mul, ← Nat.add_mul, hsum]
        omega
    · omega
    · have hexp : (jc - ja) * d = (r + jc * d) - (r + ja * d) := by
        have hsub : (jc - ja) * d = jc * d - ja * d := by rw [Nat.sub_mul]
        omega
      omega
    · have hs : r + ja * d - 1 = (r - 1) + ja * d := by omega
      rw [hs, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · omega
  · have hgt : jc < ja := by omega
    refine ⟨(r + jc * d, r + ja * d), ja - jc, ?_, ?_, ?_, ?_, ?_⟩
    · refine mem_pairSet.2 ⟨hememc.2, hmema.2, ?_, ⟨r + jb * d, hmemb.2, ?_⟩⟩
      · intro hcon
        have hcancel : ja * d = jc * d := by omega
        have : ja = jc := Nat.eq_of_mul_eq_mul_right hd0 hcancel
        omega
      · have hmul : ja * d + jc * d = jb * d + jb * d := by
          rw [← Nat.add_mul, ← Nat.add_mul, hsum]
        omega
    · omega
    · have hexp : (ja - jc) * d = (r + ja * d) - (r + jc * d) := by
        have hsub : (ja - jc) * d = ja * d - jc * d := by rw [Nat.sub_mul]
        omega
      omega
    · have hs : r + jc * d - 1 = (r - 1) + jc * d := by omega
      rw [hs, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · omega

lemma pairSet_lower {N : ℕ} {δ : ℝ} {C : Finset ℕ} (hδ : 0 < δ)
    (hC : C ⊆ Finset.Icc 1 N) (hcard : δ * (N : ℝ) ≤ (C.card : ℝ))
    (hN : 4 * mB δ ≤ N) :
    (δ / (32 * ((mB δ : ℕ) : ℝ)^3)) * N^2 ≤ ((pairSet C).card : ℝ) := by
  classical
  set m := mB δ with hmdef
  have hm1 : 1 ≤ m := mB_pos δ
  have hmR : (0:ℝ) < (m : ℝ) := by positivity
  have hmR2 : (0:ℝ) < 2 * (m : ℝ) := by positivity
  have hmR3 : (0:ℝ) < 32 * ((m : ℝ)^3) := by positivity
  -- the levels
  set D₁ := N / (2 * m) + 1 with hD₁def
  set D₂ := N / m with hD₂def
  -- per-level richness bound
  have key : ∀ d ∈ Finset.Icc D₁ D₂,
      (δ/2) * N ≤ (((Finset.Icc 1 d).filter
        (fun r => (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).card : ℝ) * (2*m) := by
    intro d hd
    have hd1 : 1 ≤ d := by
      have hD₁pos : 1 ≤ D₁ := by
        rw [hD₁def]
        have : 0 ≤ N / (2*m) := Nat.zero_le _
        omega
      have : D₁ ≤ d := (Finset.mem_Icc.1 hd).1
      omega
    have hdN : d ≤ N := by
      have hD₂le : d ≤ D₂ := (Finset.mem_Icc.1 hd).2
      have hD₂N : D₂ ≤ N := Nat.div_le_self N m
      omega
    have hD1 : N / (2 * m) + 1 ≤ d := (Finset.mem_Icc.1 hd).1
    have hmd : m * d ≤ N := by
      have hD₂le : d ≤ D₂ := (Finset.mem_Icc.1 hd).2
      have hle : D₂ * m ≤ N := Nat.div_mul_le_self N m
      have hmono : m * d ≤ m * D₂ := Nat.mul_le_mul_left m hD₂le
      have hcomm : m * D₂ = D₂ * m := Nat.mul_comm _ _
      omega
    set R := (Finset.Icc 1 d).filter
      (fun r => (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ)) with hRdef
    -- the full sum splits
    have hsplit : ∑ r ∈ R, ((C ∩ grid N d r).card:ℝ)
        + ∑ r ∈ (Finset.Icc 1 d).filter
            (fun r => ¬ ((δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))),
            ((C ∩ grid N d r).card:ℝ)
        = ∑ r ∈ Finset.Icc 1 d, ((C ∩ grid N d r).card:ℝ) :=
      Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 d)
        (fun r => (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))
        (fun r => ((C ∩ grid N d r).card:ℝ))
    -- poor grids contribute little
    have hpoor : ∑ r ∈ (Finset.Icc 1 d).filter
          (fun r => ¬ ((δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))),
          ((C ∩ grid N d r).card:ℝ) ≤ (δ/2) * N := by
      have h1 : ∀ r ∈ (Finset.Icc 1 d).filter
          (fun r => ¬ ((δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))),
          ((C ∩ grid N d r).card:ℝ) ≤ (δ/2) * ((grid N d r).card:ℝ) := by
        intro r hr
        simp only [mem_filter] at hr
        exact le_of_lt (not_le.1 hr.2)
      have h2 : ∀ r : ℕ, (δ/2) * ((grid N d r).card:ℝ) ≥ 0 := by
        intro _
        positivity
      calc ∑ r ∈ (Finset.Icc 1 d).filter
            (fun r => ¬ ((δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))),
            ((C ∩ grid N d r).card:ℝ)
          ≤ ∑ r ∈ (Finset.Icc 1 d).filter
            (fun r => ¬ ((δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))),
            (δ/2) * ((grid N d r).card:ℝ) := Finset.sum_le_sum h1
        _ ≤ ∑ r ∈ Finset.Icc 1 d, (δ/2) * ((grid N d r).card:ℝ) :=
            Finset.sum_mono_set_of_nonneg h2 (Finset.filter_subset _ _)
        _ = (δ/2) * N := by
            have hsumcast : ∑ r ∈ Finset.Icc 1 d, ((grid N d r).card:ℝ) = (N:ℝ) := by
              have hsum := sum_grid_N hd1 hdN
              exact_mod_cast hsum
            rw [← Finset.mul_sum, hsumcast]
    -- rich mass
    have hfull : ∑ r ∈ Finset.Icc 1 d, ((C ∩ grid N d r).card:ℝ) = (C.card : ℝ) := by
      have h := sum_inter_grid hd1 hdN C hC
      exact_mod_cast h
    have hrichmass : (δ/2) * N ≤ ∑ r ∈ R, ((C ∩ grid N d r).card:ℝ) := by
      have h4 : ∑ r ∈ R, ((C ∩ grid N d r).card:ℝ)
          = ∑ r ∈ Finset.Icc 1 d, ((C ∩ grid N d r).card:ℝ)
            - ∑ r ∈ (Finset.Icc 1 d).filter
              (fun r => ¬ ((δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))),
              ((C ∩ grid N d r).card:ℝ) := by
        rw [← hsplit]
        linarith
      rw [h4, hfull]
      linarith
    -- each rich grid has at most 2m elements of C
    have hcap : ∀ r ∈ R, ((C ∩ grid N d r).card:ℝ) ≤ 2 * (m:ℝ) := by
      intro r hr
      rw [hRdef] at hr
      simp only [mem_filter, Finset.mem_Icc] at hr
      obtain ⟨⟨hr1, hrd⟩, -⟩ := hr
      have hle : (grid N d r).card ≤ 2 * m := by
        have hd0 : 0 < d := by omega
        have hlen : (N - r)/d + 1 ≤ 2 * m := grid_len_le (δ := δ) (N := N) (d := d) (r := r) hd0 hr1 hD1
        rw [card_grid N d r (by omega)]
        exact hlen
      have hsub : (C ∩ grid N d r).card ≤ (grid N d r).card :=
        Finset.card_le_card (Finset.inter_subset_right)
      have h1 : ((C ∩ grid N d r).card : ℝ) ≤ ((grid N d r).card : ℝ) := by
        exact_mod_cast hsub
      have h2 : ((grid N d r).card : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
        exact_mod_cast hle
      have h3 : ((2 * m : ℕ) : ℝ) = 2 * (m:ℝ) := by push_cast; ring
      linarith
    calc (δ/2) * N ≤ ∑ r ∈ R, ((C ∩ grid N d r).card:ℝ) := hrichmass
      _ ≤ ∑ r ∈ R, 2 * (m:ℝ) := Finset.sum_le_sum hcap
      _ = (R.card : ℝ) * (2*m) := by rw [Finset.sum_const]; ring
  -- total rich count
  set RG : Finset (ℕ × ℕ) := (Finset.Icc D₁ D₂).biUnion (fun d =>
    ((Finset.Icc 1 d).filter (fun r =>
      (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).image (fun r => (d, r)))
    with hRGdef
  have hRGmem : ∀ d r : ℕ, (d, r) ∈ RG ↔ d ∈ Finset.Icc D₁ D₂ ∧ 1 ≤ r ∧ r ≤ d ∧
      (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ) := by
    intro d r
    rw [hRGdef, mem_biUnion]
    constructor
    · rintro ⟨d₀, hd₀, hmem⟩
      obtain ⟨r', hr'mem, hdeq⟩ := Finset.mem_image.1 hmem
      obtain ⟨rfl, rfl⟩ : d₀ = d ∧ r' = r := Prod.ext_iff.1 hdeq
      obtain ⟨hmem2, hrich⟩ := Finset.mem_filter.1 hr'mem
      obtain ⟨hr1, hrd⟩ := Finset.mem_Icc.1 hmem2
      exact ⟨hd₀, hr1, hrd, hrich⟩
    · rintro ⟨hdc, hr1, hrd, hrich⟩
      refine ⟨d, hdc, Finset.mem_image.2 ⟨r, ?_, rfl⟩⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hr1, hrd⟩, hrich⟩
  -- each rich grid yields a pair
  have hall : ∀ q ∈ RG, ∃ p : ℕ × ℕ, ∃ t : ℕ, p ∈ pairSet C ∧ 1 ≤ t ∧
      t * q.1 = p.2 - p.1 ∧ (p.1 - 1) % q.1 + 1 = q.2 ∧ t < 2 * m := by
    rintro ⟨d, r⟩ hq
    obtain ⟨hdc, hr1, hrd, hrich⟩ := (hRGmem d r).1 hq
    have hD₁pos : 1 ≤ D₁ := by
      rw [hD₁def]
      have : 0 ≤ N / (2*m) := Nat.zero_le _
      omega
    have hd1 : 1 ≤ d := Nat.le_trans hD₁pos (Finset.mem_Icc.1 hdc).1
    have hdN : d ≤ N := by
      have hD₂le : d ≤ D₂ := (Finset.mem_Icc.1 hdc).2
      have hD₂N : D₂ ≤ N := Nat.div_le_self N m
      omega
    have hD1 : N / (2 * m) + 1 ≤ d := (Finset.mem_Icc.1 hdc).1
    have hmd : m * d ≤ N := by
      have hD₂le : d ≤ D₂ := (Finset.mem_Icc.1 hdc).2
      have hle : D₂ * m ≤ N := Nat.div_mul_le_self N m
      have hmono : m * d ≤ m * D₂ := Nat.mul_le_mul_left m hD₂le
      have hcomm : m * D₂ = D₂ * m := Nat.mul_comm _ _
      omega
    have hrN : r ≤ N := by omega
    have hrich' : (δ/2) * (((N - r)/d + 1 : ℕ):ℝ) ≤ ((C ∩ grid N d r).card:ℝ) := by
      rw [← card_grid N d r hd1]
      exact hrich
    exact rich_grid_pair hδ hr1 hrd hd1 hrN hmd hD1 hrich'
  have hall' : ∀ a : {q // q ∈ RG}, ∃ p : ℕ × ℕ, ∃ t : ℕ, p ∈ pairSet C ∧ 1 ≤ t ∧
      t * a.val.1 = p.2 - p.1 ∧ (p.1 - 1) % a.val.1 + 1 = a.val.2 ∧ t < 2 * m := by
    intro a
    exact hall a.val a.property
  choose pw tw hpw ht1 hspan hres htlt using hall'
  -- the level count: N/(4m) ≤ number of levels
  have hAmB : N / (2*m) ≤ N / m := Nat.div_le_div_left (by omega) (by omega)
  have hcardIcc : (Finset.Icc D₁ D₂).card = N / m - N / (2*m) := by
    have h : (Finset.Icc D₁ D₂).card = D₂ + 1 - D₁ := by simp
    rw [h, hD₁def, hD₂def]
    omega
  have hcast : ((Finset.Icc D₁ D₂).card : ℝ) = ((N/m : ℕ) : ℝ) - ((N/(2*m) : ℕ) : ℝ) := by
    rw [hcardIcc, Nat.cast_sub hAmB]
  have hlevels : ((N:ℝ))/(4*(m:ℝ)) ≤ ((Finset.Icc D₁ D₂).card : ℝ) := by
    have h1 : ((N/m : ℕ) : ℝ) > (N:ℝ)/m - 1 := cast_div_gt_sub_one N m (by omega)
    have h2 : ((N/(2*m) : ℕ) : ℝ) ≤ (N:ℝ)/(2*(m:ℝ)) := by
      have h2a := cast_div_le N (2*m) (by omega)
      have h2b : ((2*m : ℕ) : ℝ) = 2*(m:ℝ) := by push_cast; ring
      rw [h2b] at h2a
      exact h2a
    have hX : (N:ℝ)/m = 4 * ((N:ℝ)/(4*(m:ℝ))) := by field_simp
    have hY : (N:ℝ)/(2*(m:ℝ)) = 2 * ((N:ℝ)/(4*(m:ℝ))) := by field_simp; ring
    have hZ : (1:ℝ) ≤ (N:ℝ)/(4*(m:ℝ)) := by
      have hcast2 : ((4*m : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
      have h4m : ((4*m : ℕ) : ℝ) = 4*(m:ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 4*(m:ℝ))]
      linarith
    rw [hcast]
    linarith
  -- RG decomposes over levels
  have hfib : (RG.card : ℝ) = ∑ d ∈ Finset.Icc D₁ D₂,
      (((Finset.Icc 1 d).filter (fun r =>
        (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).card : ℝ) := by
    have hmaps : Set.MapsTo (Prod.fst : ℕ × ℕ → ℕ) ↑RG ↑(Finset.Icc D₁ D₂) := by
      intro q hq
      simp only [Finset.mem_coe]
      obtain ⟨hdc, -⟩ := (hRGmem q.1 q.2).1 hq
      exact hdc
    have hcard : RG.card = ∑ d ∈ Finset.Icc D₁ D₂,
        (RG.filter (fun q => Prod.fst q = d)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    have heq : ∀ d ∈ Finset.Icc D₁ D₂,
        (RG.filter (fun q => Prod.fst q = d)) =
        (((Finset.Icc 1 d).filter (fun r =>
          (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).image
          (fun r => (d, r))) := by
      intro d hd
      ext q
      constructor
      · intro hq
        obtain ⟨hqRG, hqd⟩ : q ∈ RG ∧ Prod.fst q = d := Finset.mem_filter.1 hq
        obtain ⟨-, hr1, hrd, hrich⟩ := (hRGmem q.1 q.2).1 hqRG
        rw [hqd] at hrd hrich
        refine Finset.mem_image.2 ⟨q.2, ?_, ?_⟩
        · exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hr1, hrd⟩, hrich⟩
        · exact Prod.ext_iff.2 ⟨hqd.symm, rfl⟩
      · intro hq
        obtain ⟨r', hr'mem, hqr⟩ := Finset.mem_image.1 hq
        obtain ⟨rfl, rfl⟩ : d = q.1 ∧ r' = q.2 := Prod.ext_iff.1 hqr
        obtain ⟨hIcc, hrich⟩ := Finset.mem_filter.1 hr'mem
        obtain ⟨hr1, hrd⟩ := Finset.mem_Icc.1 hIcc
        exact Finset.mem_filter.2 ⟨(hRGmem q.1 q.2).2 ⟨hd, hr1, hrd, hrich⟩, rfl⟩
    calc (RG.card : ℝ) = ∑ d ∈ Finset.Icc D₁ D₂,
          ((RG.filter (fun q => Prod.fst q = d)).card : ℝ) := by
          exact_mod_cast hcard
      _ = ∑ d ∈ Finset.Icc D₁ D₂,
          ((((Finset.Icc 1 d).filter (fun r =>
            (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).image
            (fun r => (d, r))).card : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          rw [heq d hd]
      _ = ∑ d ∈ Finset.Icc D₁ D₂,
          (((Finset.Icc 1 d).filter (fun r =>
            (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).card : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro d hd
          exact_mod_cast Finset.card_image_of_injOn
            (f := fun r => (d, r)) (s := (Finset.Icc 1 d).filter (fun r =>
              (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ)))
            (by
              intro a ha b hb hab
              have h : d = d ∧ a = b := Prod.ext_iff.1 hab
              omega)
  -- sum of the per-level bounds
  have hsumbound : ((Finset.Icc D₁ D₂).card : ℝ) * ((δ/2)*(N:ℝ)) ≤ (2*(m:ℝ)) * (RG.card:ℝ) := by
    have hterm : ∀ d ∈ Finset.Icc D₁ D₂,
        ((δ/2)*(N:ℝ)) ≤ (2*(m:ℝ)) * (((Finset.Icc 1 d).filter (fun r =>
          (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).card : ℝ) :=
      fun d hd => le_trans (key d hd) (by rw [mul_comm])
    have h1 : ∑ d ∈ Finset.Icc D₁ D₂, ((δ/2)*(N:ℝ)) ≤ ∑ d ∈ Finset.Icc D₁ D₂,
        (2*(m:ℝ)) * (((Finset.Icc 1 d).filter (fun r =>
          (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).card : ℝ) :=
      Finset.sum_le_sum hterm
    have h2 : ∑ d ∈ Finset.Icc D₁ D₂, ((δ/2)*(N:ℝ))
        = ((Finset.Icc D₁ D₂).card : ℝ) * ((δ/2)*(N:ℝ)) := by
      simp [Finset.sum_const]
    have h3 : ∑ d ∈ Finset.Icc D₁ D₂, (2*(m:ℝ)) * (((Finset.Icc 1 d).filter (fun r =>
          (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).card : ℝ)
        = (2*(m:ℝ)) * ∑ d ∈ Finset.Icc D₁ D₂, (((Finset.Icc 1 d).filter (fun r =>
          (δ/2)*((grid N d r).card:ℝ) ≤ ((C ∩ grid N d r).card:ℝ))).card : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    rw [← h2, hfib, ← h3]
    exact h1
  -- the injection into pairSet × range (2m)
  have hinj : ∀ a₁ a₂ : {q // q ∈ RG}, (pw a₁, tw a₁) = (pw a₂, tw a₂) → a₁ = a₂ := by
    intro a₁ a₂ heq
    obtain ⟨heqp, heqt⟩ : pw a₁ = pw a₂ ∧ tw a₁ = tw a₂ := Prod.ext_iff.1 heq
    have hs1 := hspan a₁
    have hs2 := hspan a₂
    rw [heqp, heqt] at hs1
    have hdeq : a₁.val.1 = a₂.val.1 := by
      have h0 : (0:ℕ) < tw a₂ := ht1 a₂
      have hmid : tw a₂ * a₁.val.1 = tw a₂ * a₂.val.1 := by omega
      exact Nat.eq_of_mul_eq_mul_left h0 hmid
    have hr1' := hres a₁
    have hr2' := hres a₂
    rw [heqp, hdeq] at hr1'
    have hlast : a₁.val.2 = a₂.val.2 := by rw [← hr1', ← hr2']
    exact Subtype.ext (Prod.ext hdeq hlast)
  have himgcard : ((Finset.attach RG).image (fun a => (pw a, tw a))).card =
      (Finset.attach RG).card :=
    Finset.card_image_of_injOn (by
      intro a₁ _ a₂ _ hab
      exact hinj a₁ a₂ hab)
  have hsub : ((Finset.attach RG).image (fun a => (pw a, tw a))) ⊆
      (pairSet C) ×ˢ (Finset.range (2*m)) := by
    intro q hq
    simp only [mem_image] at hq
    obtain ⟨a, _, rfl⟩ := hq
    exact mem_product.2 ⟨hpw a, Finset.mem_range.2 (htlt a)⟩
  have hprod : ((pairSet C) ×ˢ (Finset.range (2*m))).card = (pairSet C).card * (2*m) := by
    rw [Finset.card_product, Finset.card_range]
  have hchain : (RG.card : ℝ) ≤ ((pairSet C).card : ℝ) * (2*m) := by
    calc (RG.card : ℝ) = ((Finset.attach RG).card : ℝ) := by
          exact_mod_cast (Finset.card_attach (s := RG)).symm
      _ = (((Finset.attach RG).image (fun a => (pw a, tw a))).card : ℝ) := by
          exact_mod_cast himgcard.symm
      _ ≤ (((pairSet C) ×ˢ (Finset.range (2*m))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = ((pairSet C).card : ℝ) * (2*m) := by
          exact_mod_cast hprod
  -- final algebra
  have hstep1 : ((N:ℝ))/(4*(m:ℝ)) * ((δ/2)*(N:ℝ)) ≤
      ((Finset.Icc D₁ D₂).card : ℝ) * ((δ/2)*(N:ℝ)) :=
    mul_le_mul_of_nonneg_right hlevels (by positivity)
  have hstep4 : (2*(m:ℝ)) * (RG.card:ℝ) ≤ (2*(m:ℝ)) * (((pairSet C).card : ℝ) * (2*(m:ℝ))) :=
    mul_le_mul_of_nonneg_left hchain (by positivity)
  have hchain' : ((N:ℝ)/(4*(m:ℝ))) * ((δ/2)*(N:ℝ)) ≤
      (2*(m:ℝ)) * (((pairSet C).card : ℝ) * (2*(m:ℝ))) := by
    linarith [hstep1, hsumbound, hstep4]
  have hnorm1 : ((N:ℝ)/(4*(m:ℝ))) * ((δ/2)*(N:ℝ)) =
      (4*(m:ℝ)^2) * ((δ/(32*(m:ℝ)^3)) * (N:ℝ)^2) := by
    field_simp; ring
  have hnorm2 : (2*(m:ℝ)) * (((pairSet C).card : ℝ) * (2*(m:ℝ))) =
      (4*(m:ℝ)^2) * ((pairSet C).card : ℝ) := by ring
  rw [hnorm1, hnorm2] at hchain'
  exact (mul_le_mul_iff_of_pos_left (by positivity : (0:ℝ) < 4*(m:ℝ)^2)).1 hchain'

lemma exists_star {N : ℕ} {δ : ℝ} {C : Finset ℕ} (hδ : 0 < δ)
    (hC : C ⊆ Finset.Icc 1 N) (hcard : δ * (N : ℝ) ≤ (C.card : ℝ))
    (hN : 4 * mB δ ≤ N) :
    ∃ x ∈ C, (δ / (32 * ((mB δ : ℕ) : ℝ)^3)) * (N : ℝ) ≤
      ((C.filter (fun z => z ≠ x ∧ ∃ y ∈ C, x + z = 2*y)).card : ℝ) := by
  classical
  set c := δ / (32 * ((mB δ : ℕ) : ℝ)^3) with hcdef
  have hmB1 : (1:ℕ) ≤ mB δ := mB_pos δ
  have hmBR : (0:ℝ) < ((mB δ : ℕ) : ℝ) := by
    have h1 : (0:ℕ) < mB δ := by omega
    exact_mod_cast h1
  have hden : (0:ℝ) < 32 * ((mB δ : ℕ) : ℝ)^3 :=
    mul_pos (by positivity) (pow_pos hmBR 3)
  have hcpos : (0:ℝ) < c := by rw [hcdef]; exact div_pos hδ hden
  have hNn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  by_contra hcon
  push_neg at hcon
  have hpair := pairSet_lower hδ hC hcard hN
  rw [← hcdef] at hpair
  have hCne : C.Nonempty := by
    have hNpos : (0:ℕ) < N := by omega
    have hpos : (0:ℝ) < δ * (N:ℝ) := mul_pos hδ (by exact_mod_cast hNpos)
    have hCpos : (0:ℝ) < (C.card : ℝ) := lt_of_lt_of_le hpos hcard
    exact Finset.card_pos.1 (Nat.cast_pos.1 hCpos)
  have hmaps : Set.MapsTo (Prod.fst : ℕ × ℕ → ℕ) ↑(pairSet C) ↑C := by
    intro p hp
    simp only [Finset.mem_coe]
    exact (mem_pairSet.1 hp).1
  have hfib : (pairSet C).card = ∑ x ∈ C, ((pairSet C).filter (fun p => p.1 = x)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hsub : ∀ x ∈ C, (((pairSet C).filter (fun p => p.1 = x)).image Prod.snd) ⊆
      (C.filter (fun z => z ≠ x ∧ ∃ y ∈ C, x + z = 2*y)) := by
    intro x hx z hz
    obtain ⟨p, hp_mem, hz_eq⟩ := Finset.mem_image.1 hz
    obtain ⟨hp_mem', hpx⟩ : p ∈ pairSet C ∧ p.1 = x := Finset.mem_filter.1 hp_mem
    obtain ⟨-, h2, hne, hy⟩ := mem_pairSet.1 hp_mem'
    refine Finset.mem_filter.2 ⟨hz_eq ▸ h2, ⟨?_, ?_⟩⟩
    · rw [← hz_eq, ← hpx]; exact hne.symm
    · obtain ⟨y, hyC, hyp⟩ := hy
      refine ⟨y, hyC, ?_⟩
      rw [← hpx, ← hz_eq]
      exact hyp
  have hcardimg : ∀ x ∈ C, ((pairSet C).filter (fun p => p.1 = x)).card =
      (((pairSet C).filter (fun p => p.1 = x)).image Prod.snd).card := by
    intro x hx
    refine (Finset.card_image_of_injOn ?_).symm
    intro a ha b hb hab
    have ha' : a.1 = x := (Finset.mem_filter.1 ha).2
    have hb' : b.1 = x := (Finset.mem_filter.1 hb).2
    exact Prod.ext (by rw [ha', hb']) hab
  have hsumR : ((pairSet C).card : ℝ) = ∑ x ∈ C,
      (((pairSet C).filter (fun p => p.1 = x)).card : ℝ) := by
    exact_mod_cast hfib
  have hle : ∑ x ∈ C, (((pairSet C).filter (fun p => p.1 = x)).card : ℝ) ≤
      ∑ x ∈ C, ((C.filter (fun z => z ≠ x ∧ ∃ y ∈ C, x + z = 2*y)).card : ℝ) := by
    refine Finset.sum_le_sum (fun x hx => ?_)
    have h1 := hsub x hx
    have h2 := hcardimg x hx
    have h3 : (((pairSet C).filter (fun p => p.1 = x)).image Prod.snd).card ≤
        (C.filter (fun z => z ≠ x ∧ ∃ y ∈ C, x + z = 2*y)).card :=
      Finset.card_le_card h1
    exact_mod_cast ((le_of_eq h2).trans h3)
  have hstrict : ∑ x ∈ C, ((C.filter (fun z => z ≠ x ∧ ∃ y ∈ C, x + z = 2*y)).card : ℝ) <
      (C.card : ℝ) * (c * (N:ℝ)) := by
    have h2 : ∑ x ∈ C, ((C.filter (fun z => z ≠ x ∧ ∃ y ∈ C, x + z = 2*y)).card : ℝ) <
        ∑ x ∈ C, (c * (N:ℝ)) :=
      Finset.sum_lt_sum_of_nonempty hCne (fun x hx => hcon x hx)
    have h3 : ∑ x ∈ C, (c * (N:ℝ)) = (C.card : ℝ) * (c * (N:ℝ)) := by
      simp [Finset.sum_const]
    linarith
  have hCN : (C.card : ℝ) ≤ (N:ℝ) := by
    have h1 : C.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hC
    have h2 : (Finset.Icc 1 N).card = N := by simp
    rw [h2] at h1
    exact_mod_cast h1
  have h4 : (C.card : ℝ) * (c * (N:ℝ)) ≤ (N:ℝ) * (c * (N:ℝ)) :=
    mul_le_mul_of_nonneg_right hCN (mul_nonneg hcpos.le hNn)
  have h5 : (N:ℝ) * (c * (N:ℝ)) = c * (N:ℝ)^2 := by ring
  linarith

lemma star_step {N : ℕ} {δ : ℝ} {C : Finset ℕ} (hδ : 0 < δ)
    (hC : C ⊆ Finset.Icc 1 N) (hcard : δ * (N : ℝ) ≤ (C.card : ℝ))
    (hN : 4 * mB δ ≤ N) :
    ∃ x ∈ C, ∃ C' : Finset ℕ, C' ⊆ C ∧
      (δ / (32 * ((mB δ : ℕ) : ℝ)^3)) * (N : ℝ) ≤ (C'.card : ℝ) ∧
      ∀ z ∈ C', z ≠ x ∧ ∃ y ∈ C, x + z = 2*y := by
  obtain ⟨x, hx, hxle⟩ := exists_star hδ hC hcard hN
  refine ⟨x, hx, C.filter (fun z => z ≠ x ∧ ∃ y ∈ C, x + z = 2*y),
    fun z hz => (Finset.mem_filter.1 hz).1, hxle, ?_⟩
  intro z hz
  exact (Finset.mem_filter.1 hz).2

/-- The density sequence for the star recursion. -/
noncomputable def dens (δ : ℝ) : ℕ → ℝ
  | 0 => δ
  | j+1 => dens δ j / (32 * ((mB (dens δ j) : ℕ) : ℝ)^3)

lemma dens_zero (δ : ℝ) : dens δ 0 = δ := rfl

lemma dens_succ (δ : ℝ) (j : ℕ) :
    dens δ (j+1) = dens δ j / (32 * ((mB (dens δ j) : ℕ) : ℝ)^3) := rfl

lemma mB_cast_pos (ρ : ℝ) : (0:ℝ) < ((mB ρ : ℕ) : ℝ) := by
  have h2 := mB_pos ρ
  have h1 : (0:ℕ) < mB ρ := by omega
  exact_mod_cast h1

lemma dens_pos {δ : ℝ} (hδ : 0 < δ) : ∀ j, 0 < dens δ j := by
  intro j
  induction j with
  | zero => rw [dens_zero]; exact hδ
  | succ j ih =>
    rw [dens_succ]
    exact div_pos ih (mul_pos (by positivity) (pow_pos (mB_cast_pos _) 3))

/-- The star recursion: k steps of `star_step` produce k centers with all midpoints in D. -/
lemma star_chain {N k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hN : ∀ j ≤ k, 4 * mB (dens δ j) ≤ N)
    {D : Finset ℕ} (hDIcc : D ⊆ Finset.Icc 1 N) (hDcard : δ * (N:ℝ) ≤ (D.card : ℝ)) :
    ∃ (L : List ℕ), L.length = k ∧ L.Nodup ∧ (∀ x ∈ L, x ∈ D) ∧
      (∀ x ∈ L, ∀ z ∈ L, x ≠ z → ∃ y ∈ D, x + z = 2*y) := by
  have main : ∀ j : ℕ, j ≤ k → ∃ (L : List ℕ) (C' : Finset ℕ),
      L.length = j ∧ L.Nodup ∧
      (∀ x ∈ L, x ∈ D) ∧
      (∀ x ∈ L, x ∉ C') ∧
      (∀ x ∈ L, ∀ z ∈ L, x ≠ z → ∃ y ∈ D, x + z = 2*y) ∧
      (∀ x ∈ L, ∀ z ∈ C', ∃ y ∈ D, x + z = 2*y) ∧
      C' ⊆ D ∧ (dens δ j)*(N:ℝ) ≤ (C'.card : ℝ) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨[], D, rfl, List.nodup_nil, ?_, ?_, ?_, ?_, le_refl D, ?_⟩
      · intro x hx
        simp at hx
      · intro x hx
        simp at hx
      · intro x hx z hz hxz
        simp at hx
      · intro x hx
        simp at hx
      · rw [dens_zero]
        exact hDcard
    | succ j ih =>
      intro hjk
      obtain ⟨L, C', hlen, hnd, hLD, hLout, hLpair, hLfuture, hC'D, hC'card⟩ :=
        ih (le_trans (Nat.le_succ j) hjk)
      have hdens := dens_pos hδ j
      obtain ⟨x, hxC', C'', hC''C', hC''card, hC''prop⟩ :=
        star_step (δ := dens δ j) hdens (hC'D.trans hDIcc) hC'card
          (hN j (le_trans (Nat.le_succ j) hjk))
      have hxnotinL : x ∉ L := by
        intro hxin
        exact hLout x hxin hxC'
      have hnewcard : dens δ (j+1) * (N:ℝ) ≤ (C''.card : ℝ) := by
        rw [dens_succ]
        exact hC''card
      refine ⟨x :: L, C'', by simp [hlen], List.nodup_cons.2 ⟨hxnotinL, hnd⟩, ?_, ?_, ?_, ?_,
        hC''C'.trans hC'D, hnewcard⟩
      · intro a ha
        by_cases hax : a = x
        · subst a
          exact hC'D hxC'
        · have haL : a ∈ L := (List.mem_cons.1 ha).resolve_left hax
          exact hLD a haL
      · intro a ha hain
        by_cases hax : a = x
        · subst a
          obtain ⟨hne, -⟩ := hC''prop x hain
          exact hne rfl
        · have haL : a ∈ L := (List.mem_cons.1 ha).resolve_left hax
          exact hLout a haL (hC''C' hain)
      · intro a ha z hz haz
        by_cases hax : a = x
        · subst a
          by_cases hzx : z = x
          · subst z
            exact absurd haz (fun h => h rfl)
          · have hzL : z ∈ L := (List.mem_cons.1 hz).resolve_left hzx
            obtain ⟨y, hyD, hyp⟩ := hLfuture z hzL x hxC'
            exact ⟨y, hyD, by rw [Nat.add_comm]; exact hyp⟩
        · have haL : a ∈ L := (List.mem_cons.1 ha).resolve_left hax
          by_cases hzx : z = x
          · subst z
            obtain ⟨y, hyD, hyp⟩ := hLfuture a haL x hxC'
            exact ⟨y, hyD, hyp⟩
          · have hzL : z ∈ L := (List.mem_cons.1 hz).resolve_left hzx
            exact hLpair a haL z hzL haz
      · intro a ha z hz
        by_cases hax : a = x
        · subst a
          obtain ⟨-, hy⟩ := hC''prop z hz
          obtain ⟨y, hyC', hyp⟩ := hy
          exact ⟨y, hC'D hyC', hyp⟩
        · have haL : a ∈ L := (List.mem_cons.1 ha).resolve_left hax
          obtain ⟨y, hyD, hyp⟩ := hLfuture a haL z (hC''C' hz)
          exact ⟨y, hyD, hyp⟩
  obtain ⟨L, C', hlen, hnd, hLD, -, hLpair, -, -, -⟩ := main k (le_refl k)
  exact ⟨L, hlen, hnd, hLD, hLpair⟩

/-- Case 2: many doubling pairs gives the k-clique. -/
lemma case2_clique {N k : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    {ε : ℝ} (hε : 0 < ε) (hN : ∀ j ≤ k, 4 * mB (dens ε j) ≤ N)
    (hDcard : ε * (N:ℝ) ≤ ((A.filter (fun a => 2*a ≤ N ∧ 2*a ∈ A)).card : ℝ)) :
    ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A := by
  set D := A.filter (fun a => 2*a ≤ N ∧ 2*a ∈ A) with hDdef
  have hDIcc : D ⊆ Finset.Icc 1 N := (Finset.filter_subset (p := fun a => 2*a ≤ N ∧ 2*a ∈ A) A).trans hA
  obtain ⟨L, hlen, hnd, hLD, hLpair⟩ := star_chain hε hN hDIcc hDcard
  refine ⟨L.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have hxD : x ∈ D := hLD x (List.mem_toFinset.1 hx)
    exact (Finset.mem_filter.1 hxD).1
  · rw [List.toFinset_card_of_nodup hnd]
    exact hlen
  · intro x hx z hz hxz
    obtain ⟨y, hyD, hyp⟩ :=
      hLpair x (List.mem_toFinset.1 hx) z (List.mem_toFinset.1 hz) hxz
    have hyA : 2*y ∈ A := ((Finset.mem_filter.1 hyD).2).2
    rw [hyp]
    exact hyA

/-- The N-threshold for the star recursion. -/
noncomputable def Nbig (δ : ℝ) (k : ℕ) : ℕ :=
  ((Finset.range (k+1)).image (fun j => 4 * mB (dens δ j))).max'
    (⟨4 * mB (dens δ 0), Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), rfl⟩⟩)

lemma le_Nbig (δ : ℝ) (k j : ℕ) (hj : j ≤ k) : 4 * mB (dens δ j) ≤ Nbig δ k := by
  refine Finset.le_max' ((Finset.range (k+1)).image (fun j => 4 * mB (dens δ j))) _ ?_
  exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), rfl⟩

end Star

open Finset Filter

lemma two_mul_add_one_le_pow (m : ℕ) (hm : 3 ≤ m) : 2*m + 1 ≤ 2^m := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases h3 : 3 ≤ m
      · have ih' := ih h3
        have : 2*(m+1)+1 ≤ 2 * (2*m+1) := by omega
        have hp : 2^m * 2 = 2^(m+1) := by rw [pow_succ]
        nlinarith
      · have hmle : m ≤ 2 := by omega
        interval_cases m <;> omega

lemma log_le_div_pow (m N : ℕ) (hm : 3 ≤ m) (hN : 2 ^ (3*m+4) ≤ N) :
    Nat.log 2 N ≤ N / 2^m := by
  have h2 : 1 < (2:ℕ) := by omega
  have hdle : 2 ^ (2*m) ≤ N := by
    apply le_trans _ hN
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 2*m ≤ 3*m+4)
  have hlogd : 2*m ≤ Nat.log 2 N := by
    have := Nat.log_monotone (b := 2) hdle
    simpa [Nat.log_pow h2 (2*m)] using this
  have hlogeq0 := Nat.log_div_base_pow 2 N (2*m)
  have hlogeq : Nat.log 2 N = Nat.log 2 (N / 2^(2*m)) + 2*m := by omega
  rw [hlogeq]
  set q := N / 2^(2*m)
  have hq : 2 ^ (m+4) ≤ q := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < 2) _)]
    have hpoweq : 2 ^ (m+4) * 2 ^ (2*m) = 2 ^ (3*m+4) := by
      rw [← pow_add]
      congr 1
      omega
    simpa [q, hpoweq] using hN
  have hlogq : Nat.log 2 q ≤ q := Nat.log_le_self _ _
  have hq1 : 1 ≤ q := by
    have hp : 0 < 2^(m+4) := pow_pos (by omega : 0 < 2) _
    omega
  have hmlepow : 2*m + 1 ≤ 2^m := two_mul_add_one_le_pow m hm
  have h2mle : 2*m ≤ (2^m - 1) * q := by
    have h2mle' : 2*m ≤ 2^m - 1 := by omega
    have : 2^m - 1 ≤ (2^m - 1) * q := by
      exact Nat.le_mul_of_pos_right _ hq1
    omega
  have hsmall : q + 2*m ≤ 2^m * q := by
    have hqle : q ≤ 2^m * q := Nat.le_mul_of_pos_left q (by positivity)
    have hcalc : q + (2^m - 1) * q = 2^m * q := by
      rw [Nat.mul_sub_right_distrib]
      rw [one_mul]
      exact Nat.add_sub_cancel' hqle
    rw [← hcalc]
    exact Nat.add_le_add_left h2mle q
  have hdivq : (N / 2^m) / 2^m = q := by
    rw [Nat.div_div_eq_div_mul]
    rw [show 2^m * 2^m = 2^(2*m) by rw [← pow_add]; congr 1; omega]
  have hmul := Nat.mul_div_le (N / 2^m) (2^m)
  rw [hdivq] at hmul
  have hbig : 2^m * q ≤ N / 2^m := by simpa [Nat.mul_comm] using hmul
  exact le_trans (le_trans (Nat.add_le_add_right hlogq (2*m)) hsmall) hbig


lemma aux_mul_bound {A0 L j M P N : ℝ}
    (hA0nn : 0 ≤ A0) (hPnn : 0 ≤ P) (hLnn : 0 ≤ L) (hMnn : 0 ≤ M)
    (hA0 : A0 ≤ (5/4:ℝ) * P) (hL' : L * P ≤ N / 4) (hM' : M * P ≤ N / 32)
    (hj : j ≤ M) (hA0s : A0 ≤ N / 16) :
    A0 * (2 * L + 2 * j + 1) ≤ N := by
  have hterm1 : A0 * (2 * L) ≤ (5/8:ℝ) * N := by
    calc
      A0 * (2 * L) ≤ ((5/4:ℝ) * P) * (2 * L) :=
        mul_le_mul_of_nonneg_right hA0 (by nlinarith only [hLnn])
      _ = (5/2:ℝ) * (L * P) := by ring
      _ ≤ (5/2:ℝ) * (N / 4) := mul_le_mul_of_nonneg_left hL' (by norm_num)
      _ = (5/8:ℝ) * N := by ring
  have hterm2 : A0 * (2 * j) ≤ (5/64:ℝ) * N := by
    calc
      A0 * (2 * j) ≤ A0 * (2 * M) :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hj]) hA0nn
      _ ≤ ((5/4:ℝ) * P) * (2 * M) :=
        mul_le_mul_of_nonneg_right hA0 (by nlinarith only [hMnn])
      _ = (5/2:ℝ) * (M * P) := by ring
      _ ≤ (5/2:ℝ) * (N / 32) := mul_le_mul_of_nonneg_left hM' (by norm_num)
      _ = (5/64:ℝ) * N := by ring
  have hNnn : 0 ≤ N := by nlinarith only [hA0nn, hA0s]
  have hdecomp : A0 * (2 * L + 2 * j + 1) = A0 * (2 * L) + A0 * (2 * j) + A0 := by ring
  rw [hdecomp]
  nlinarith only [hterm1, hterm2, hA0s, hNnn]

set_option maxHeartbeats 2000000 in
lemma case1_clique {N k : ℕ} (hk : 3 ≤ k)
    (hNlarge : 2 ^ (3*(4*k+50)+4) ≤ N)
    {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hcard : ((2:ℝ)/3 - (1 / ((k:ℝ)^2 * (2:ℝ)^(2*k+30)))) * (N:ℝ) ≤ (A.card:ℝ))
    (hDlt : (((A.filter (fun a => 2*a ∈ A)).card : ℕ) : ℝ) <
      1 / ((k:ℝ)^2 * (2:ℝ)^(2*k+30)) * (N:ℝ)) :
    ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A := by
  classical
  let ε : ℝ := 1 / ((k:ℝ)^2 * (2:ℝ)^(2*k+30))
  have hkposN : 0 < k := by omega
  have hkposR : 0 < (k:ℝ) := by exact_mod_cast hkposN
  have hdenpos : 0 < (k:ℝ)^2 * (2:ℝ)^(2*k+30) := by positivity
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hNpos : 0 < N := by
    have hp : 0 < 2 ^ (3*(4*k+50)+4) := pow_pos (by omega : 0 < 2) _
    omega
  have hklt : k ≤ 2^k := by
    have := Nat.lt_two_pow_self (n := k)
    omega
  have hkltR : (k:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast hklt
  have hk2le : (k:ℝ)^2 ≤ (2:ℝ)^(2*k+10) := by
    have hs : (k:ℝ)^2 ≤ ((2:ℝ)^k)^2 := by nlinarith [sq_nonneg ((2:ℝ)^k - (k:ℝ))]
    rw [← pow_mul] at hs
    have heq : k * 2 = 2 * k := by omega
    rw [heq] at hs
    have hp : (2:ℝ)^(2*k) ≤ (2:ℝ)^(2*k+10) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hdenle1 : (k:ℝ)^2 * (2:ℝ)^(2*k+30) ≤ (2:ℝ)^(4*k+40) := by
    have hp : 0 < (2:ℝ)^(2*k+30) := pow_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_right hk2le (le_of_lt hp)
    have hpoweq : (2:ℝ)^(2*k+10) * (2:ℝ)^(2*k+30) = (2:ℝ)^(4*k+40) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpoweq] at hmul
    exact hmul
  have hdenle2 : (k:ℝ)^2 * (2:ℝ)^(2*k+30) ≤ (2:ℝ)^(4*k+49) := by
    have hp : (2:ℝ)^(4*k+40) ≤ (2:ℝ)^(4*k+49) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact le_trans hdenle1 hp
  have hepsge1 : (1:ℝ)/(2:ℝ)^(4*k+40) ≤ ε := by
    dsimp [ε]
    exact one_div_le_one_div_of_le (by positivity : (0:ℝ) < (k:ℝ)^2 * (2:ℝ)^(2*k+30)) hdenle1
  have hepsge2 : (2:ℝ)/(2:ℝ)^(4*k+50) ≤ ε := by
    have hpowsplit : (2:ℝ)^(4*k+50) = 2 * (2:ℝ)^(4*k+49) := by
      rw [show (4*k+50:ℕ) = (4*k+49)+1 by omega, pow_succ]
      ring
    have hpow : (2:ℝ)/(2:ℝ)^(4*k+50) = 1/(2:ℝ)^(4*k+49) := by
      rw [hpowsplit]
      field_simp
    rw [hpow]
    exact one_div_le_one_div_of_le (by positivity : (0:ℝ) < (k:ℝ)^2 * (2:ℝ)^(2*k+30)) hdenle2
  set mlog := 4*k+50
  have hmlog3 : 3 ≤ mlog := by dsimp [mlog]; omega
  have hlogle : Nat.log 2 N ≤ N / 2^mlog := log_le_div_pow mlog N hmlog3 (by simpa [mlog] using hNlarge)
  have hq2 : 2 ≤ N / 2^mlog := by
    rw [Nat.le_div_iff_mul_le (pow_pos (by omega : 0 < 2) _)]
    have hsmall : 2 * 2^mlog ≤ 2^(mlog+2) := by
      have hle : 2 * 2^mlog ≤ 4 * 2^mlog := Nat.mul_le_mul_right _ (by norm_num)
      have heq : 4 * 2^mlog = 2^(mlog+2) := by
        rw [show (4:ℕ) = 2^2 by norm_num, ← pow_add]
        congr 1
        omega
      simpa [heq] using hle
    have hbig : 2^(mlog+2) ≤ 2^(3*mlog+4) := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
    exact le_trans hsmall (le_trans hbig (by simpa [mlog] using hNlarge))
  have hlogplusNat : Nat.log 2 N + 2 ≤ (N / 2^mlog) + (N / 2^mlog) := by omega
  have hlogplusFloor : ((Nat.log 2 N : ℕ) : ℝ) + 2 ≤ 2 * ((N / 2^mlog : ℕ) : ℝ) := by
    have h' : (((Nat.log 2 N + 2 : ℕ) : ℝ) ≤ ((N / 2^mlog + N / 2^mlog : ℕ) : ℝ)) := by
      exact_mod_cast hlogplusNat
    norm_num at h' ⊢
    simpa [two_mul] using h'
  have hfloorle : ((N / 2^mlog : ℕ) : ℝ) ≤ (N:ℝ) / (2:ℝ)^mlog := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using Chn.cast_div_le N (2^mlog) (pow_pos (by omega : 0 < 2) _)
  have hlogplus : ((Nat.log 2 N : ℕ) : ℝ) + 2 ≤ ε * (N:ℝ) := by
    have h1 : 2 * ((N / 2^mlog : ℕ) : ℝ) ≤ 2 * ((N:ℝ) / (2:ℝ)^mlog) := by nlinarith
    have h2 : 2 * ((N:ℝ) / (2:ℝ)^mlog) ≤ ε * (N:ℝ) := by
      have hNnr : 0 ≤ (N:ℝ) := by positivity
      have := mul_le_mul_of_nonneg_right hepsge2 hNnr
      have hpowpos : (0:ℝ) < (2:ℝ)^mlog := by positivity
      rw [div_eq_mul_inv] at this ⊢
      nlinarith
    linarith
  set D : Finset ℕ := A.filter (fun a => 2*a ∈ A) with hDdef
  set B : Finset ℕ := A \ D with hBdef
  have hDsub : D ⊆ A := by rw [hDdef]; exact Finset.filter_subset _ _
  have hBsub : B ⊆ Finset.Icc 1 N := by rw [hBdef]; exact (Finset.sdiff_subset.trans hA)
  have hindB : ∀ m ∈ B, 2*m ≤ N → 2*m ∉ B := by
    intro m hm h2m hcon
    have hmDfalse : m ∉ D := (Finset.mem_sdiff.1 (by simpa [hBdef] using hm)).2
    have h2mA : 2*m ∈ A := (Finset.mem_sdiff.1 (by simpa [hBdef] using hcon)).1
    exact hmDfalse (by rw [hDdef]; exact Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 (by simpa [hBdef] using hm)).1, h2mA⟩)
  set bad : Finset ℕ := ((Finset.Icc 1 N).image Chn.od).filter
      (fun u => (B.filter (fun m => Chn.od m = u)).card < (Nat.log 2 (N/u)+2)/2) with hbaddef
  set Ev : Finset ℕ := (Finset.Icc 1 N).filter (fun m => Chn.dv m % 2 = 0) with hEvdef
  have hbadle0 := Chn.bad_le_deficit B hBsub hindB
  have hbadle0Nat : bad.card + B.card ≤ Ev.card := by
    simpa [bad, Ev] using hbadle0
  have hbadle0' : (bad.card : ℝ) + (B.card : ℝ) ≤ (Ev.card : ℝ) := by
    exact_mod_cast hbadle0Nat
  have hBcardNat : B.card = A.card - D.card := by
    rw [hBdef, Finset.card_sdiff, Finset.inter_eq_left.mpr hDsub]
  have hDleA : D.card ≤ A.card := Finset.card_le_card hDsub
  have hBcardR : (B.card : ℝ) = (A.card : ℝ) - (D.card : ℝ) := by
    rw [hBcardNat]
    norm_num [Nat.cast_sub hDleA]
  have hEvle : (Ev.card : ℝ) ≤ (2:ℝ)/3 * (N:ℝ) + ((Nat.log 2 N : ℕ) : ℝ) + 2 := by
    simpa [Ev] using Chn.ebound (N := N) (by omega : 1 ≤ N)
  have hcard' : ((2:ℝ)/3 - ε) * (N:ℝ) ≤ (A.card:ℝ) := by simpa [ε] using hcard
  have hDlt' : (D.card : ℝ) < ε * (N:ℝ) := by simpa [D, hDdef, ε] using hDlt
  have hbadR : (bad.card : ℝ) ≤ 3 * ε * (N:ℝ) := by
    linarith [hbadle0', hBcardR, hEvle, hcard', hDlt', hlogplus]
  let f : ℕ → ℕ := fun d => 1 + 2^(2*d)
  let A0 : ℕ := 2^(2*k) + 2^(2*k-2)
  let L : ℕ := N / 2^(2*k+2)
  let M : ℕ := N / 2^(2*k+5)
  let J : Finset ℕ := Finset.Icc 1 M
  let u : ℕ → ℕ := fun j => 2*(L+j)+1
  let C : Finset ℕ := J.image u
  let Forb : Finset ℕ := bad ∪ (Finset.Icc 1 (k-1)).biUnion (fun d => bad.image (fun b => b / f d))
  have hsmallpow : 2^(2*k+5) ≤ N := by
    have hp : 2^(2*k+5) ≤ 2^(3*(4*k+50)+4) := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
    exact le_trans hp hNlarge
  have hMpos : 0 < M := Nat.div_pos hsmallpow (pow_pos (by omega : 0 < 2) _)
  have hCcard : C.card = M := by
    rw [show C = J.image u by rfl]
    rw [Finset.card_image_of_injOn]
    · simp [J, hMpos]
    · intro a ha b hb hab
      dsimp [u] at hab
      omega
  have hForbcard : Forb.card ≤ k * bad.card := by
    set R : Finset ℕ := (Finset.Icc 1 (k-1)).biUnion (fun d => bad.image (fun b => b / f d)) with hR
    have hRcard : R.card ≤ (k-1) * bad.card := by
      calc
        R.card ≤ ∑ d ∈ Finset.Icc 1 (k-1), (bad.image (fun b => b / f d)).card := by
          rw [hR]
          exact Finset.card_biUnion_le
        _ ≤ ∑ d ∈ Finset.Icc 1 (k-1), bad.card := by
          exact Finset.sum_le_sum (fun d hd => Finset.card_image_le)
        _ = (k-1) * bad.card := by
          simp [Nat.card_Icc]
    have hunion : Forb.card ≤ bad.card + R.card := by
      rw [show Forb = bad ∪ R by rfl]
      exact Finset.card_union_le _ _
    calc
      Forb.card ≤ bad.card + R.card := hunion
      _ ≤ bad.card + (k-1) * bad.card := Nat.add_le_add_left hRcard _
      _ = k * bad.card := by
        have hkdecomp : k = (k-1) + 1 := by omega
        rw [hkdecomp, Nat.add_mul]
        simp [Nat.add_comm]
  have hcoef : 3 * (k:ℝ) * ε ≤ 1 / (2:ℝ)^(2*k+7) := by
    dsimp [ε]
    have hden : (0:ℝ) < (k:ℝ)^2 * (2:ℝ)^(2*k+30) := by positivity
    rw [div_eq_mul_inv]
    field_simp
    have h23 : (3:ℝ) ≤ (2:ℝ)^23 := by norm_num
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    have hpowrel : (2:ℝ)^(2*k+30) = (2:ℝ)^(2*k+7) * (2:ℝ)^23 := by
      rw [show (2*k+30:ℕ) = (2*k+7)+23 by omega, pow_add]
    rw [hpowrel]
    have hpnonneg : 0 ≤ (2:ℝ)^(2*k+7) := by positivity
    have hmul := mul_le_mul_of_nonneg_left h23 hpnonneg
    have hprodnonneg : 0 ≤ (2:ℝ)^(2*k+7) * (2:ℝ)^23 := by positivity
    have hk23 : (2:ℝ)^(2*k+7) * (2:ℝ)^23 ≤ (k:ℝ) * ((2:ℝ)^(2*k+7) * (2:ℝ)^23) := by
      simpa using mul_le_mul_of_nonneg_right hk1 hprodnonneg
    nlinarith
  have hNdivM : (N:ℝ)/(2:ℝ)^(2*k+7) < (M:ℝ) := by
    have hgt' : (N:ℝ)/(2:ℝ)^(2*k+5) - 1 < (M:ℝ) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        Star.cast_div_gt_sub_one N (2^(2*k+5)) (pow_pos (by omega : 0 < 2) _)
    have hge4' : (4:ℝ) ≤ (N:ℝ)/(2:ℝ)^(2*k+5) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(2*k+5))]
      have hpowNat : 2^(2*k+7) ≤ N := by
        have hp : 2^(2*k+7) ≤ 2^(3*mlog+4) := Nat.pow_le_pow_right (by omega : 0 < 2) (by dsimp [mlog]; omega)
        exact le_trans hp (by simpa [mlog] using hNlarge)
      have hpowR : (2:ℝ)^(2*k+7) ≤ (N:ℝ) := by exact_mod_cast hpowNat
      have hrel : (2:ℝ)^(2*k+7) = 4 * (2:ℝ)^(2*k+5) := by
        rw [show (2*k+7:ℕ) = (2*k+5)+2 by omega, pow_add]
        norm_num
        ring
      simpa [hrel] using hpowR
    have hdiff' : (N:ℝ)/(2:ℝ)^(2*k+7) ≤ (N:ℝ)/(2:ℝ)^(2*k+5) - 1 := by
      have hrel : (2:ℝ)^(2*k+7) = 4 * (2:ℝ)^(2*k+5) := by
        rw [show (2*k+7:ℕ) = (2*k+5)+2 by omega, pow_add]
        norm_num
        ring
      rw [hrel]
      rw [show (N:ℝ) / (4 * (2:ℝ)^(2*k+5)) = ((N:ℝ) / (2:ℝ)^(2*k+5)) / 4 by ring]
      nlinarith [hge4']
    exact lt_of_le_of_lt hdiff' hgt'
  have hForb_lt : Forb.card < C.card := by
    have h1 : ((k * bad.card : ℕ) : ℝ) ≤ (3*(k:ℝ))*ε*(N:ℝ) := by
      rw [Nat.cast_mul]
      have hk_nonneg : 0 ≤ (k:ℝ) := by positivity
      have hbad_nonneg : 0 ≤ (bad.card:ℝ) := by positivity
      have hbad_nonneg' : 0 ≤ (3:ℝ)*ε*(N:ℝ) := by
        have hNnr : 0 ≤ (N:ℝ) := by positivity
        positivity
      have hmul := mul_le_mul_of_nonneg_left hbadR hk_nonneg
      nlinarith [hmul]
    have h2 : (3*(k:ℝ))*ε*(N:ℝ) ≤ (N:ℝ)/(2:ℝ)^(2*k+7) := by
      have hNnr : 0 ≤ (N:ℝ) := by positivity
      have := mul_le_mul_of_nonneg_right hcoef hNnr
      rw [div_eq_mul_inv] at this ⊢
      nlinarith
    have h3 : ((k * bad.card : ℕ) : ℝ) < (M:ℝ) := lt_of_le_of_lt (le_trans h1 h2) hNdivM
    have h4 : k * bad.card < M := by exact_mod_cast h3
    rw [hCcard]
    exact lt_of_le_of_lt hForbcard h4
  obtain ⟨j, hjJ, hjuForb⟩ : ∃ j ∈ J, u j ∉ Forb := by
    by_contra hnone
    have hall : ∀ j ∈ J, u j ∈ Forb := by
      intro j hj
      by_contra hnot
      exact hnone ⟨j, hj, hnot⟩
    have hsub : C ⊆ Forb := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hy
      exact hall j hj
    have hcardle := Finset.card_le_card hsub
    omega
  have hj1 : 1 ≤ j := (Finset.mem_Icc.1 hjJ).1
  have hjM : j ≤ M := (Finset.mem_Icc.1 hjJ).2
  have hLle : ((L:ℕ):ℝ) * ((4:ℝ)*(2:ℝ)^(2*k)) ≤ (N:ℝ) := by
    have h := Chn.cast_div_le N (2^(2*k+2)) (pow_pos (by omega : 0 < 2) _)
    have hpow : ((2^(2*k+2):ℕ):ℝ) = (4:ℝ)*(2:ℝ)^(2*k) := by
      rw [Nat.cast_pow, show (2*k+2:ℕ) = 2*k+2 by rfl, pow_add]
      norm_num
      ring
    rw [hpow] at h
    have hp : (0:ℝ) < (4:ℝ)*(2:ℝ)^(2*k) := by positivity
    rw [le_div_iff₀ hp] at h
    simpa only [L] using h
  have hMle : ((M:ℕ):ℝ) * ((32:ℝ)*(2:ℝ)^(2*k)) ≤ (N:ℝ) := by
    have h := Chn.cast_div_le N (2^(2*k+5)) (pow_pos (by omega : 0 < 2) _)
    have hpow : ((2^(2*k+5):ℕ):ℝ) = (32:ℝ)*(2:ℝ)^(2*k) := by
      rw [Nat.cast_pow, show (2*k+5:ℕ) = 2*k+5 by rfl, pow_add]
      norm_num
      ring
    rw [hpow] at h
    have hp : (0:ℝ) < (32:ℝ)*(2:ℝ)^(2*k) := by positivity
    rw [le_div_iff₀ hp] at h
    simpa only [M] using h
  have hA0eq : (4:ℕ) * A0 = 5 * 2^(2*k) := by
    dsimp [A0]
    have hsplit : 2^(2*k) = 4 * 2^(2*k-2) := by
      rw [show (2*k:ℕ) = (2*k-2)+2 by omega, pow_add]
      norm_num
      ring
    rw [hsplit]
    ring
  have hA0le : ((A0:ℕ):ℝ) ≤ ((5:ℝ)/4)*(2:ℝ)^(2*k) := by
    have h := congrArg (fun n : ℕ => (n:ℝ)) hA0eq
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at h
    have hmul : (4:ℝ) * ((A0:ℕ):ℝ) ≤ 5 * (2:ℝ)^(2*k) := by
      rw [h]
      norm_num
    calc
      ((A0:ℕ):ℝ) = ((4:ℝ) * ((A0:ℕ):ℝ)) / 4 := by ring
      _ ≤ (5 * (2:ℝ)^(2*k)) / 4 := by exact div_le_div_of_nonneg_right hmul (by norm_num)
      _ = ((5:ℝ)/4) * (2:ℝ)^(2*k) := by ring
  have hA0small : (16:ℝ)*((A0:ℕ):ℝ) ≤ (N:ℝ) := by
    have hA0pow : A0 ≤ 2^(2*k+1) := by
      dsimp [A0]
      have : 2^(2*k-2) ≤ 2^(2*k) := Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
      omega
    have hp : 16 * 2^(2*k+1) = 2^(2*k+5) := by
      rw [show (16:ℕ) = 2^4 by norm_num, ← pow_add]
      congr 1
      omega
    have hnat : 16 * A0 ≤ N := by
      calc
        16 * A0 ≤ 16 * 2^(2*k+1) := Nat.mul_le_mul_left 16 hA0pow
        _ = 2^(2*k+5) := hp
        _ ≤ N := hsmallpow
    exact_mod_cast hnat
  have hu_odd : ¬ 2 ∣ u j := by dsimp [u]; omega
  have hupos : 0 < u j := by dsimp [u]; omega
  have htmp : A0 * u j ≤ N := by
    have htmpR : ((A0 * u j : ℕ) : ℝ) ≤ (N:ℝ) := by
      rw [Nat.cast_mul]
      have huEq : ((u j : ℕ) : ℝ) = 2*(L:ℝ) + 2*(j:ℝ) + 1 := by
        dsimp [u]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        ring
      rw [huEq]
      have hjR : (j:ℝ) ≤ (M:ℝ) := by exact_mod_cast hjM
      have hL' : ((L:ℕ):ℝ) * (2:ℝ)^(2*k) ≤ (N:ℝ)/4 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
        nlinarith only [hLle]
      have hM' : ((M:ℕ):ℝ) * (2:ℝ)^(2*k) ≤ (N:ℝ)/32 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 32)]
        nlinarith only [hMle]
      have hterm3 : ((A0:ℕ):ℝ) ≤ (N:ℝ)/16 := by nlinarith only [hA0small]
      exact aux_mul_bound (A0 := (A0:ℝ)) (L := (L:ℝ)) (j := (j:ℝ)) (M := (M:ℝ))
        (P := (2:ℝ)^(2*k)) (N := (N:ℝ))
        (Nat.cast_nonneg A0) (pow_nonneg (by norm_num) _) (Nat.cast_nonneg L) (Nat.cast_nonneg M)
        hA0le hL' hM' hjR hterm3
    exact_mod_cast htmpR
  have huN : u j ≤ N := by
    have hA0pos : 0 < A0 := by dsimp [A0]; positivity
    have h1 : u j ≤ A0 * u j := Nat.le_mul_of_pos_left (u j) hA0pos
    exact le_trans h1 htmp
  have hBsubA : B ⊆ A := by rw [hBdef]; exact Finset.sdiff_subset
  have hpowA0 : 2^(2*k) ≤ A0 := by dsimp [A0]; omega
  have hAu : u j * 2^(2*k) ≤ N := by
    calc
      u j * 2^(2*k) = 2^(2*k) * u j := Nat.mul_comm _ _
      _ ≤ A0 * u j := Nat.mul_le_mul_right (u j) hpowA0
      _ ≤ N := htmp
  have hNlt0 : N < (L+1) * 2^(2*k+2) := by
    have hdpos : 0 < 2^(2*k+2) := pow_pos (by omega : 0 < 2) _
    have hdecomp : N = L * 2^(2*k+2) + N % 2^(2*k+2) := by
      rw [show L = N / 2^(2*k+2) by rfl]
      simpa [Nat.mul_comm] using (Nat.div_add_mod N (2^(2*k+2))).symm
    have hmodlt : N % 2^(2*k+2) < 2^(2*k+2) := Nat.mod_lt N hdpos
    rw [hdecomp]
    have hlt : L * 2^(2*k+2) + N % 2^(2*k+2) < L * 2^(2*k+2) + 2^(2*k+2) :=
      Nat.add_lt_add_left hmodlt _
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hlt
  have hu_ge : 2*L+2 ≤ u j := by dsimp [u]; omega
  have hNlt_final : N < u j * 2^(2*k+1) := by
    calc
      N < (L+1) * 2^(2*k+2) := hNlt0
      _ = (2*L+2) * 2^(2*k+1) := by
        have hp : 2^(2*k+2) = 2 * 2^(2*k+1) := by
          rw [show (2*k+2:ℕ) = (2*k+1)+1 by omega, pow_succ]
          ring
        rw [hp]
        ring
      _ ≤ u j * 2^(2*k+1) := Nat.mul_le_mul_right _ hu_ge
  have hNu_pos : 0 < N / u j := Nat.div_pos huN hupos
  have hlogu : Nat.log 2 (N / u j) = 2*k := by
    rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, ne_of_gt hNu_pos⟩)]
    constructor
    · rw [Nat.le_div_iff_mul_le hupos]
      simpa [Nat.mul_comm] using hAu
    · rw [Nat.div_lt_iff_lt_mul hupos]
      simpa [Nat.mul_comm] using hNlt_final
  have humod : u j % 2 = 1 := by
    have hltm : u j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hne : u j % 2 ≠ 0 := by
      intro h0
      exact hu_odd (Nat.dvd_iff_mod_eq_zero.mpr h0)
    omega
  have hodu : Chn.od (u j) = u j := by
    unfold Chn.od
    rw [Chn.dv_eq_zero hu_odd]
    simp
  have himage_u : u j ∈ (Finset.Icc 1 N).image Chn.od := by
    refine Finset.mem_image.mpr ⟨u j, ?_, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, huN⟩
    · simpa [hodu]
  have hunotbad : u j ∉ bad := by
    intro hb
    exact hjuForb (by dsimp [Forb]; exact Finset.mem_union.mpr (Or.inl hb))
  have hS_u_card0 : (Nat.log 2 (N / u j)+2)/2 ≤ (B.filter (fun m => Chn.od m = u j)).card := by
    rw [hbaddef, Finset.mem_filter] at hunotbad
    have hnotlt : ¬ (B.filter (fun m => Chn.od m = u j)).card < (Nat.log 2 (N / u j)+2)/2 := by
      intro hlt
      exact hunotbad ⟨himage_u, hlt⟩
    omega
  let Su : Finset ℕ := B.filter (fun m => Chn.od m = u j)
  have hSu_card : (Nat.log 2 (N / u j)+2)/2 ≤ Su.card := by simpa [Su] using hS_u_card0
  have hSu_sub : Su ⊆ Chn.ch N (u j) := by
    intro m hm
    have hmfilter : m ∈ B.filter (fun x => Chn.od x = u j) := by simpa [Su] using hm
    have hm' := Finset.mem_filter.1 hmfilter
    have hmod : Chn.od m = u j := hm'.2
    have hmIcc := hBsub hm'.1
    have hmch := Chn.mem_ch_of_mem_Icc (Finset.mem_Icc.1 hmIcc).1 (Finset.mem_Icc.1 hmIcc).2
    simpa [hmod] using hmch
  have hSu_hind : ∀ m ∈ Su, 2*m ≤ N → 2*m ∉ Su := by
    intro m hm h2m hcon
    have hmfilter : m ∈ B.filter (fun x => Chn.od x = u j) := by simpa [Su] using hm
    have h2filter : 2*m ∈ B.filter (fun x => Chn.od x = u j) := by simpa [Su] using hcon
    exact hindB m (Finset.mem_filter.1 hmfilter).1 h2m (Finset.mem_filter.1 h2filter).1
  have hforcing_u : ∀ e, e < Nat.log 2 (N/u j)+1 → e%2=0 → u j*2^e ∈ Su :=
    Chn.chain_forcing hupos hu_odd huN Su hSu_sub hSu_hind
      (by simp [hlogu]) (by simpa [hlogu] using hSu_card)
  have hpair : ∀ {a b : ℕ}, a < b → b < k →
      u j * 2^(2*a) + u j * 2^(2*b) ∈ A := by
    intro a b hab hbk
    let d := b-a
    have hd1 : 1 ≤ d := by dsimp [d]; omega
    have hdkm1 : d ≤ k-1 := by dsimp [d]; omega
    have hdIcc : d ∈ Finset.Icc 1 (k-1) := Finset.mem_Icc.mpr ⟨hd1, hdkm1⟩
    let v := u j * f d
    have hfdpos : 0 < f d := by dsimp [f]; positivity
    have hvpos : 0 < v := by dsimp [v]; exact Nat.mul_pos hupos hfdpos
    have hdk : d ≤ k := by omega
    have hpow_eq : f d * 2^(2*(k-d)) = 2^(2*k) + 2^(2*k-2*d) := by
      dsimp [f]
      rw [Nat.add_mul, one_mul]
      have h1 : 2^(2*d) * 2^(2*(k-d)) = 2^(2*k) := by
        rw [← pow_add]
        congr 1
        omega
      have h2 : 2^(2*(k-d)) = 2^(2*k-2*d) := by congr 1; omega
      rw [h1, h2]
      ac_rfl
    have hpow_le_A0 : f d * 2^(2*(k-d)) ≤ A0 := by
      rw [hpow_eq]
      dsimp [A0]
      apply Nat.add_le_add_left
      exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 2*k-2*d ≤ 2*k-2)
    have hvpow_le_N : v * 2^(2*(k-d)) ≤ N := by
      dsimp [v]
      calc
        (u j * f d) * 2^(2*(k-d)) = u j * (f d * 2^(2*(k-d))) := by ring
        _ ≤ u j * A0 := Nat.mul_le_mul_left (u j) hpow_le_A0
        _ = A0 * u j := Nat.mul_comm _ _
        _ ≤ N := htmp
    have hvN : v ≤ N := by
      have hpowpos : 0 < 2^(2*(k-d)) := pow_pos (by omega : 0 < 2) _
      exact le_trans (Nat.le_mul_of_pos_right v hpowpos) hvpow_le_N
    have hbase_le : 2^(2*d) ≤ f d := by dsimp [f]; omega
    have hpow_split : 2^(2*k+1) = 2^(2*d) * 2^(2*(k-d)+1) := by
      rw [← pow_add]
      congr 1
      omega
    have hvpow_gt_N : N < v * 2^(2*(k-d)+1) := by
      have hle : u j * 2^(2*k+1) ≤ v * 2^(2*(k-d)+1) := by
        rw [hpow_split]
        dsimp [v]
        calc
          u j * (2^(2*d) * 2^(2*(k-d)+1)) ≤ u j * (f d * 2^(2*(k-d)+1)) :=
            Nat.mul_le_mul_left (u j) (Nat.mul_le_mul_right _ hbase_le)
          _ = (u j * f d) * 2^(2*(k-d)+1) := by ring
      exact lt_of_lt_of_le hNlt_final hle
    have hNv_pos : 0 < N / v := Nat.div_pos hvN hvpos
    have hlogv : Nat.log 2 (N / v) = 2*(k-d) := by
      rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, ne_of_gt hNv_pos⟩)]
      constructor
      · rw [Nat.le_div_iff_mul_le hvpos]
        simpa [Nat.mul_comm] using hvpow_le_N
      · rw [Nat.div_lt_iff_lt_mul hvpos]
        simpa [Nat.mul_comm] using hvpow_gt_N
    have hfdmod : f d % 2 = 1 := by
      have hdiv : 2 ∣ 2^(2*d) := by
        have hs : 2*d = (2*d-1)+1 := by omega
        rw [hs, pow_succ]
        simpa [Nat.mul_comm] using (dvd_mul_right 2 (2^(2*d-1)))
      have hzero : 2^(2*d) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
      dsimp [f]
      omega
    have hfdodd : ¬ 2 ∣ f d := by
      intro h
      have hz : f d % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      omega
    have hvmod : v % 2 = 1 := by
      dsimp [v]
      rw [Nat.mul_mod, humod, hfdmod]
    have hvodd : ¬ 2 ∣ v := by
      intro h
      have hz : v % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      omega
    have hodv : Chn.od v = v := by
      unfold Chn.od
      rw [Chn.dv_eq_zero hvodd]
      simp
    have himage_v : v ∈ (Finset.Icc 1 N).image Chn.od := by
      refine Finset.mem_image.mpr ⟨v, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by omega, hvN⟩
      · simpa [hodv]
    have hvdiv : v / f d = u j := by
      dsimp [v]
      rw [Nat.mul_comm]
      exact Nat.mul_div_right (u j) hfdpos
    have hvnotbad : v ∉ bad := by
      intro hvbad
      apply hjuForb
      dsimp [Forb]
      apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      exact ⟨d, hdIcc, Finset.mem_image.mpr ⟨v, hvbad, hvdiv⟩⟩
    have hSv_card0 : (Nat.log 2 (N/v)+2)/2 ≤ (B.filter (fun m => Chn.od m = v)).card := by
      rw [hbaddef, Finset.mem_filter] at hvnotbad
      have hnotlt : ¬ (B.filter (fun m => Chn.od m = v)).card < (Nat.log 2 (N/v)+2)/2 := by
        intro hlt
        exact hvnotbad ⟨himage_v, hlt⟩
      omega
    let Sv : Finset ℕ := B.filter (fun m => Chn.od m = v)
    have hSv_card : (Nat.log 2 (N/v)+2)/2 ≤ Sv.card := by simpa [Sv] using hSv_card0
    have hSv_sub : Sv ⊆ Chn.ch N v := by
      intro m hm
      have hmfilter : m ∈ B.filter (fun x => Chn.od x = v) := by simpa [Sv] using hm
      have hm' := Finset.mem_filter.1 hmfilter
      have hmod : Chn.od m = v := hm'.2
      have hmIcc := hBsub hm'.1
      have hmch := Chn.mem_ch_of_mem_Icc (Finset.mem_Icc.1 hmIcc).1 (Finset.mem_Icc.1 hmIcc).2
      simpa [hmod] using hmch
    have hSv_hind : ∀ m ∈ Sv, 2*m ≤ N → 2*m ∉ Sv := by
      intro m hm h2m hcon
      have hmfilter : m ∈ B.filter (fun x => Chn.od x = v) := by simpa [Sv] using hm
      have h2filter : 2*m ∈ B.filter (fun x => Chn.od x = v) := by simpa [Sv] using hcon
      exact hindB m (Finset.mem_filter.1 hmfilter).1 h2m (Finset.mem_filter.1 h2filter).1
    have hforcing_v : ∀ e, e < Nat.log 2 (N/v)+1 → e%2=0 → v*2^e ∈ Sv :=
      Chn.chain_forcing hvpos hvodd hvN Sv hSv_sub hSv_hind
        (by simp [hlogv]) (by simpa [hlogv] using hSv_card)
    have he_lt : 2*a < Nat.log 2 (N/v)+1 := by rw [hlogv]; dsimp [d]; omega
    have hmemSv := hforcing_v (2*a) he_lt (by omega)
    have hmemfilter : v * 2^(2*a) ∈ B.filter (fun x => Chn.od x = v) := by simpa [Sv] using hmemSv
    have hmemA : v * 2^(2*a) ∈ A := hBsubA (Finset.mem_filter.1 hmemfilter).1
    have hsum : u j * 2^(2*a) + u j * 2^(2*b) = v * 2^(2*a) := by
      dsimp [v, f, d]
      have hbsp : 2*b = 2*(b-a) + 2*a := by omega
      rw [hbsp, pow_add]
      ring
    simpa [hsum] using hmemA
  let T : Finset ℕ := (Finset.range k).image (fun d => u j * 2^(2*d))
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
    have hdlt : d < k := Finset.mem_range.1 hd
    have hmem := hforcing_u (2*d) (by rw [hlogu]; omega) (by omega)
    have hmemfilter : u j * 2^(2*d) ∈ B.filter (fun x => Chn.od x = u j) := by simpa [Su] using hmem
    exact hBsubA (Finset.mem_filter.1 hmemfilter).1
  · change ((Finset.range k).image (fun d => u j * 2^(2*d))).card = k
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      have hpowe : 2^(2*a) = 2^(2*b) := Nat.eq_of_mul_eq_mul_left hupos hab
      have hexp : 2*a = 2*b := Nat.pow_right_injective (by norm_num) hpowe
      omega
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    have ha_lt : a < k := Finset.mem_range.1 ha
    have hb_lt : b < k := Finset.mem_range.1 hb
    have habne : a ≠ b := by
      intro hEq
      apply hxy
      subst b
      rfl
    rcases lt_or_gt_of_ne habne with hab | hba
    · exact hpair hab hb_lt
    · simpa [Nat.add_comm] using hpair hba ha_lt

end OMA

theorem OMA.solution : type_of% @Erdos865.erdos_865.variants.upper_bound := by
  intro k hk
  let ε₀ : ℝ := 1 / ((k:ℝ)^2 * (2:ℝ)^(2*k+30))
  have hε₀pos : 0 < ε₀ := by dsimp [ε₀]; positivity
  have hkge9 : (9:ℝ) ≤ (k:ℝ)^2 * (2:ℝ)^(2*k+30) := by
    have hk3 : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hk2ge : (9:ℝ) ≤ (k:ℝ)^2 := by nlinarith [sq_nonneg ((k:ℝ) - 3)]
    have hpge : (1:ℝ) ≤ (2:ℝ)^(2*k+30) := one_le_pow₀ (by norm_num)
    simpa using mul_le_mul hk2ge hpge (by positivity) (by norm_num)
  have hε₀le : ε₀ ≤ (1:ℝ)/9 := by
    dsimp [ε₀]
    exact one_div_le_one_div_of_le (by norm_num) hkge9
  have hcoef_nonneg : 0 ≤ (2:ℝ)/3 - ε₀ := by nlinarith
  refine ⟨ε₀/2, by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (Star.Nbig ε₀ k),
    Filter.eventually_ge_atTop (2^(3*(4*k+50)+4)),
    Filter.eventually_ge_atTop (Nat.ceil ((4:ℝ)/ε₀))] with N hNbig hNlarge hNeps
  let m : ℕ := Nat.ceil ((2/3 - ε₀) * (N:ℝ))
  have hm_lower : (2/3 - ε₀) * (N:ℝ) ≤ (m:ℝ) := by
    dsimp [m]
    exact Nat.le_ceil _
  have hm_upper : (m:ℝ) < (2/3 - ε₀) * (N:ℝ) + 1 := by
    dsimp [m]
    exact Nat.ceil_lt_add_one (mul_nonneg hcoef_nonneg (by positivity))
  have hNepsR : (4:ℝ)/ε₀ ≤ (N:ℝ) := by
    have h1 : (4:ℝ)/ε₀ ≤ (Nat.ceil ((4:ℝ)/ε₀) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil ((4:ℝ)/ε₀) : ℝ) ≤ (N:ℝ) := by exact_mod_cast hNeps
    exact le_trans h1 h2
  have hslack : (2:ℝ) ≤ (ε₀/2) * (N:ℝ) := by
    have hmul : ε₀ * ((4:ℝ)/ε₀) ≤ ε₀ * (N:ℝ) :=
      mul_le_mul_of_nonneg_left hNepsR (le_of_lt hε₀pos)
    have heq : ε₀ * ((4:ℝ)/ε₀) = 4 := by field_simp [ne_of_gt hε₀pos]
    nlinarith
  have hm_upper2 : (m:ℝ) + 1 ≤ (2/3 - ε₀/2) * (N:ℝ) := by
    nlinarith [hm_upper, hslack]
  have hm_mem : m ∈ {m : ℕ | ∀ A ⊆ Finset.Icc 1 N, A.card ≥ m →
      ∃ S ⊆ A, S.card = k ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x + y ∈ A} := by
    intro A hA hAcard
    have hAcardR : (2/3 - ε₀) * (N:ℝ) ≤ (A.card:ℝ) := by
      have hmcard : (m:ℝ) ≤ (A.card:ℝ) := by exact_mod_cast hAcard
      exact le_trans hm_lower hmcard
    have hD_eq : A.filter (fun a => 2*a ∈ A) =
        A.filter (fun a => 2*a ≤ N ∧ 2*a ∈ A) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact ⟨h.1, (Finset.mem_Icc.1 (hA h.2)).2, h.2⟩
      · intro h
        exact ⟨h.1, h.2.2⟩
    by_cases hDlt : (((A.filter (fun a => 2*a ∈ A)).card : ℕ) : ℝ) < ε₀ * (N:ℝ)
    ·       exact OMA.case1_clique hk hNlarge hA (by simpa [ε₀] using hAcardR) hDlt
    · have hDcard : ε₀ * (N:ℝ) ≤ ((A.filter (fun a => 2*a ≤ N ∧ 2*a ∈ A)).card : ℝ) := by
        rw [← hD_eq]
        exact le_of_not_gt hDlt
      have hNall : ∀ j ≤ k, 4 * Star.mB (Star.dens ε₀ j) ≤ N := by
        intro j hj
        exact le_trans (Star.le_Nbig ε₀ k j hj) hNbig
      exact Star.case2_clique hA hε₀pos hNall hDcard
  have hflem : Erdos865.f N k ≤ m := by
    unfold Erdos865.f
    exact Nat.sInf_le hm_mem
  have hfR : (Erdos865.f N k : ℝ) ≤ (m:ℝ) := by exact_mod_cast hflem
  nlinarith [hfR, hm_upper2]
