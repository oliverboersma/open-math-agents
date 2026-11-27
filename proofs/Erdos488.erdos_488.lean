import FormalConjectures.ErdosProblems.«488»
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
Adapted from the Lean disproof by Alicien B., licensed Apache-2.0.
Source: https://github.com/Alicienn/erdos-488-lean/blob/96b5360fc220ef583b0455b9392b21af442f8b06/Erdos488/Disproof.lean
Paper: https://aixiv.online/pdf/2611.02020v2
Ported to the pinned Formal Conjectures statement and Left to Solve checker.
-/

namespace OMA.Erdos488Port

open scoped Classical

/-- The 53 odd primes `≤ 256`. -/
def oddPrimes256 : List ℕ :=
  [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

lemma oddPrimes256_length : oddPrimes256.length = 53 := by decide

set_option maxRecDepth 20000 in
lemma oddPrimes256_prime : ∀ p ∈ oddPrimes256, Nat.Prime p := by decide

lemma oddPrimes256_odd : ∀ p ∈ oddPrimes256, p % 2 = 1 := by decide

lemma oddPrimes256_nodup : oddPrimes256.Nodup := by decide

set_option maxRecDepth 20000 in
lemma prime_le_256_mem_aux :
    ∀ p ∈ List.range 257, Nat.Prime p → p ≠ 2 → p ∈ oddPrimes256 := by decide

lemma prime_le_256_mem (p : ℕ) (hp : Nat.Prime p) (hle : p ≤ 256) (hne2 : p ≠ 2) :
    p ∈ oddPrimes256 :=
  prime_le_256_mem_aux p (List.mem_range.mpr (by omega)) hp hne2

/-- Product of all odd primes `≤ 256`, marked irreducible after evaluation so tactics never unfold it. -/
irreducible_def Q256 : ℕ := oddPrimes256.prod

/-- Euler's totient of `Q256`, written as `∏ (p - 1)`. -/
irreducible_def phiQ256 : ℕ := (oddPrimes256.map (· - 1)).prod

lemma Q256_pos : 0 < Q256 := by
  rw [Q256_def]
  apply List.prod_pos
  intro p hp
  exact (oddPrimes256_prime p hp).pos

lemma phiQ256_pos : 0 < phiQ256 := by
  rw [phiQ256_def]
  apply List.prod_pos
  intro x hx
  rcases List.mem_map.mp hx with ⟨p, hp, rfl⟩
  have := (oddPrimes256_prime p hp).two_le
  omega

/-- Key numerical separation: `216 * Q256 < 1280 * phiQ256`. -/
lemma key_totient_ineq : 216 * Q256 < 1280 * phiQ256 := by
  rw [Q256_def, phiQ256_def]
  unfold oddPrimes256
  decide

/-- Telescoping numerical bound: `5^3500 * 28009^53 < 6^3500` (factored as `70 * 50` so exponents `< 256`). -/
lemma key_telescope_ineq : 5 ^ 3500 * 28009 ^ 53 < 6 ^ 3500 := by
  have h5 : (5 : ℕ) ^ 3500 = (5 ^ 70) ^ 50 := by rw [← pow_mul]
  have h6 : (6 : ℕ) ^ 3500 = (6 ^ 70) ^ 50 := by rw [← pow_mul]
  rw [h5, h6]
  norm_num

/-- Totient of a duplicate-free product of primes equals `∏ (p - 1)`. -/
lemma totient_prod_primes :
    ∀ (L : List ℕ), (∀ p ∈ L, Nat.Prime p) → L.Nodup →
      Nat.totient L.prod = (L.map (· - 1)).prod
  | [], _, _ => by simp
  | p :: L, hpr, hnd => by
    rw [List.nodup_cons] at hnd
    have hp : Nat.Prime p := hpr p List.mem_cons_self
    have hprL : ∀ q ∈ L, Nat.Prime q := fun q hq => hpr q (List.mem_cons_of_mem p hq)
    have hcop : Nat.Coprime p L.prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro q hq
      have hq_pr : Nat.Prime q := hprL q hq
      rw [Nat.coprime_primes hp hq_pr]
      intro heq
      subst heq
      exact hnd.1 hq
    simp only [List.prod_cons, List.map_cons]
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, totient_prod_primes L hprL hnd.2]

lemma totient_Q256 : Nat.totient Q256 = phiQ256 := by
  rw [Q256_def, phiQ256_def]
  exact totient_prod_primes oddPrimes256 oddPrimes256_prime oddPrimes256_nodup

/-- An integer `t ≥ 1` is `256`-smooth if every prime factor of `t` is `≤ 256`. -/
def isSmooth256 (t : ℕ) : Prop :=
  1 ≤ t ∧ ∀ p : ℕ, Nat.Prime p → p ∣ t → p ≤ 256

/-- Finite set of odd `256`-smooth integers in `[1, y]`. -/
noncomputable def oddSmooth (y : ℕ) : Finset ℕ :=
  (Finset.Icc 1 y).filter (fun w => w % 2 = 1 ∧ isSmooth256 w)

lemma mem_oddSmooth_iff {w y : ℕ} :
    w ∈ oddSmooth y ↔ (1 ≤ w ∧ w ≤ y) ∧ w % 2 = 1 ∧ isSmooth256 w := by
  unfold oddSmooth
  rw [Finset.mem_filter, Finset.mem_Icc]

lemma one_mem_oddSmooth {y : ℕ} (hy : 1 ≤ y) : 1 ∈ oddSmooth y := by
  rw [mem_oddSmooth_iff]
  refine ⟨⟨le_rfl, hy⟩, by norm_num, le_rfl, ?_⟩
  intro p hp hdvd
  have : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
  have := hp.two_le
  omega

/-- Box bound: `|oddSmooth (2^T)| ≤ (T + 1)^53` via prime factorization injection. -/
lemma oddSmooth_pow_two_le (T : ℕ) : (oddSmooth (2 ^ T)).card ≤ (T + 1) ^ 53 := by
  let f : ℕ → (Fin oddPrimes256.length → Fin (T + 1)) := fun w i =>
    let p := oddPrimes256.get i
    ⟨min (w.factorization p) T, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hinj : Set.InjOn f (oddSmooth (2 ^ T) : Set ℕ) := by
    intro w₁ hw₁ w₂ hw₂ hfeq
    rw [Finset.mem_coe, mem_oddSmooth_iff] at hw₁ hw₂
    rcases hw₁ with ⟨⟨hw₁_ge1, hw₁_le⟩, hw₁_odd, hw₁_sm⟩
    rcases hw₂ with ⟨⟨hw₂_ge1, hw₂_le⟩, hw₂_odd, hw₂_sm⟩
    have hw₁0 : w₁ ≠ 0 := by omega
    have hw₂0 : w₂ ≠ 0 := by omega
    have hexp_le : ∀ w, 1 ≤ w → w ≤ 2 ^ T → ∀ p, Nat.Prime p → w.factorization p ≤ T := by
      intro w hw1 hwt p hp
      have hdvd : p ^ (w.factorization p) ∣ w := Nat.ordProj_dvd w p
      have hpow_le : 2 ^ (w.factorization p) ≤ 2 ^ T := by
        calc 2 ^ (w.factorization p) ≤ p ^ (w.factorization p) :=
            Nat.pow_le_pow_left hp.two_le _
          _ ≤ w := Nat.le_of_dvd hw1 hdvd
          _ ≤ 2 ^ T := hwt
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
    apply Nat.factorization_inj hw₁0 hw₂0
    ext p
    by_cases hp : Nat.Prime p
    · by_cases hp2 : p = 2
      · subst hp2
        have hnd1 : ¬ (2 ∣ w₁) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
        have hnd2 : ¬ (2 ∣ w₂) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
        rw [Nat.factorization_eq_zero_of_not_dvd hnd1, Nat.factorization_eq_zero_of_not_dvd hnd2]
      · by_cases hple : p ≤ 256
        · have hmem : p ∈ oddPrimes256 := prime_le_256_mem p hp hple hp2
          rcases List.mem_iff_get.mp hmem with ⟨idx, rfl⟩
          have hi : f w₁ idx = f w₂ idx := congr_fun hfeq idx
          dsimp only [f] at hi
          injection hi with hi_val
          have hle1 := hexp_le w₁ hw₁_ge1 hw₁_le (oddPrimes256.get idx) hp
          have hle2 := hexp_le w₂ hw₂_ge1 hw₂_le (oddPrimes256.get idx) hp
          rwa [min_eq_left hle1, min_eq_left hle2] at hi_val
        · have hnd1 : ¬ (p ∣ w₁) := fun hd => hple (hw₁_sm.2 p hp hd)
          have hnd2 : ¬ (p ∣ w₂) := fun hd => hple (hw₂_sm.2 p hp hd)
          rw [Nat.factorization_eq_zero_of_not_dvd hnd1, Nat.factorization_eq_zero_of_not_dvd hnd2]
    · rw [Nat.factorization_eq_zero_of_not_prime w₁ hp,
          Nat.factorization_eq_zero_of_not_prime w₂ hp]
  calc (oddSmooth (2 ^ T)).card
      ≤ (Finset.univ : Finset (Fin oddPrimes256.length → Fin (T + 1))).card :=
        Finset.card_le_card_of_injOn f (fun _ _ => Finset.mem_univ _) hinj
    _ = (T + 1) ^ oddPrimes256.length := by simp
    _ = (T + 1) ^ 53 := by rw [oddPrimes256_length]

/-- Existence of a good dyadic scale `j ∈ [1, 3500]` where `5 * O(2^(8*(j+1))) ≤ 6 * O(2^(8*j))`. -/
lemma exists_good_scale :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 3500 ∧
      5 * (oddSmooth (2 ^ (8 * (j + 1)))).card ≤ 6 * (oddSmooth (2 ^ (8 * j))).card := by
  by_contra hall
  have hall' : ∀ j : ℕ, 1 ≤ j → j ≤ 3500 →
      6 * (oddSmooth (2 ^ (8 * j))).card < 5 * (oddSmooth (2 ^ (8 * (j + 1)))).card := by
    intro j hj1 hj2
    by_contra hle
    exact hall ⟨j, hj1, hj2, by omega⟩
  have hstep : ∀ k : ℕ, k ≤ 3500 →
      6 ^ k * (oddSmooth (2 ^ (8 * 1))).card ≤ 5 ^ k * (oddSmooth (2 ^ (8 * (k + 1)))).card := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have ihk := ih (by omega)
      have hgt := hall' (k + 1) (by omega) (by omega)
      calc 6 ^ (k + 1) * (oddSmooth (2 ^ (8 * 1))).card
          = 6 * (6 ^ k * (oddSmooth (2 ^ (8 * 1))).card) := by ring
        _ ≤ 6 * (5 ^ k * (oddSmooth (2 ^ (8 * (k + 1)))).card) := Nat.mul_le_mul_left 6 ihk
        _ = 5 ^ k * (6 * (oddSmooth (2 ^ (8 * (k + 1)))).card) := by ring
        _ ≤ 5 ^ k * (5 * (oddSmooth (2 ^ (8 * (k + 2)))).card) :=
            Nat.mul_le_mul_left (5 ^ k) (Nat.le_of_lt hgt)
        _ = 5 ^ (k + 1) * (oddSmooth (2 ^ (8 * (k + 2)))).card := by ring
  have h3500 := hstep 3500 le_rfl
  have h1 : 1 ≤ (oddSmooth (2 ^ (8 * 1))).card :=
    Finset.card_pos.mpr ⟨1, one_mem_oddSmooth (by norm_num)⟩
  have hbox := oddSmooth_pow_two_le (8 * (3500 + 1))
  have h28009 : 8 * (3500 + 1) + 1 = 28009 := by norm_num
  rw [h28009] at hbox
  have hcontra : 6 ^ 3500 ≤ 5 ^ 3500 * 28009 ^ 53 := by
    calc 6 ^ 3500 ≤ 6 ^ 3500 * (oddSmooth (2 ^ (8 * 1))).card := Nat.le_mul_of_pos_right _ h1
      _ ≤ 5 ^ 3500 * (oddSmooth (2 ^ (8 * (3500 + 1)))).card := h3500
      _ ≤ 5 ^ 3500 * 28009 ^ 53 := Nat.mul_le_mul_left _ hbox
  exact absurd key_telescope_ineq (not_lt_of_ge hcontra)

/-- Every positive integer `t` factors uniquely as `2^(t.factorization 2) * oddPart(t)` with odd part odd. -/
lemma two_pow_mul_odd_part {t : ℕ} (ht : 1 ≤ t) :
    2 ^ (t.factorization 2) * (t / 2 ^ (t.factorization 2)) = t ∧
      (t / 2 ^ (t.factorization 2)) % 2 = 1 ∧
      1 ≤ t / 2 ^ (t.factorization 2) := by
  set e := t.factorization 2
  set w := t / 2 ^ e
  have ht0 : t ≠ 0 := by omega
  have hdvd : 2 ^ e ∣ t := Nat.ordProj_dvd t 2
  have hmul : 2 ^ e * w = t := Nat.mul_div_cancel' hdvd
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    omega
  have hnd : ¬ (2 ∣ w) := Nat.not_dvd_ordCompl (by decide : Nat.Prime 2) ht0
  rw [Nat.dvd_iff_mod_eq_zero] at hnd
  have hw_odd : w % 2 = 1 := by omega
  have hw_ge1 : 1 ≤ w := Nat.pos_of_ne_zero hw0
  exact ⟨hmul, hw_odd, hw_ge1⟩

/-- Upper bound at `n = 256 * x`: for `A = (Ico x (2*x)).filter isSmooth256`,
`|B ∩ [1, 256 * x]| ≤ 9 * |oddSmooth (256 * x)|`. -/
lemma upper_bound_at_n {x : ℕ} (hx : 2 ≤ x) :
    let A := (Finset.Ico x (2 * x)).filter isSmooth256
    let n := 256 * x
    let B := {k ≥ 1 | ∃ a ∈ A, a ∣ k}
    ((Finset.Icc 1 n).filter (· ∈ B)).card ≤ 9 * (oddSmooth n).card := by
  intro A n B
  let S := (Finset.Icc x n).filter isSmooth256
  have hsub : (Finset.Icc 1 n).filter (· ∈ B) ⊆ S := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_Icc] at ht
    rcases ht with ⟨⟨ht1, htn⟩, hB⟩
    rcases hB with ⟨_, a, haA, q, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Ico] at haA
    rcases haA with ⟨⟨hax, _⟩, hasm⟩
    have hq1 : 1 ≤ q := by
      by_contra hq0
      have : q = 0 := by omega
      subst this
      omega
    change a * q ≤ 256 * x at htn
    have hq256 : q ≤ 256 := by nlinarith
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith, htn⟩, ht1, ?_⟩
    intro p hp hdvd
    rcases hp.dvd_mul.mp hdvd with hpa | hpq
    · exact hasm.2 p hp hpa
    · exact le_trans (Nat.le_of_dvd hq1 hpq) hq256
  have hS_le : S.card ≤ (oddSmooth n ×ˢ Finset.range 9).card := by
    have hex_e0 : ∀ w : ℕ, 1 ≤ w → ∃ e : ℕ, x ≤ 2 ^ e * w := by
      intro w hw
      refine ⟨x, ?_⟩
      have hlt : x < 2 ^ x := Nat.lt_two_pow_self
      nlinarith
    let e0 : ℕ → ℕ := fun w => if hw : 1 ≤ w then Nat.find (hex_e0 w hw) else 0
    let g : ℕ → ℕ × ℕ := fun t =>
      let e := t.factorization 2
      let w := t / 2 ^ e
      (w, e - e0 w)
    apply Finset.card_le_card_of_injOn g
    · intro t ht
      change t ∈ (Finset.Icc x n).filter isSmooth256 at ht
      rw [Finset.mem_filter, Finset.mem_Icc] at ht
      rcases ht with ⟨⟨htx, htn⟩, htsm⟩
      have ht1 : 1 ≤ t := by omega
      obtain ⟨hmul, hwodd, hw1⟩ := two_pow_mul_odd_part ht1
      set e := t.factorization 2
      set w := t / 2 ^ e
      have hwn : w ≤ n := by
        have h2pos : 1 ≤ 2 ^ e := Nat.one_le_pow e 2 (by norm_num)
        nlinarith
      have hwsm : isSmooth256 w := by
        refine ⟨hw1, fun p hp hpw => htsm.2 p hp ?_⟩
        rw [← hmul]
        exact dvd_mul_of_dvd_right hpw _
      have he0_spec : x ≤ 2 ^ (e0 w) * w := by
        dsimp only [e0]
        rw [dif_pos hw1]
        exact Nat.find_spec (hex_e0 w hw1)
      have he_ge : e0 w ≤ e := by
        dsimp only [e0]
        rw [dif_pos hw1]
        apply Nat.find_min' (hex_e0 w hw1)
        linarith
      have he_lt : e - e0 w < 9 := by
        by_contra hge9
        have he9 : e0 w + 9 ≤ e := by omega
        have hpow9 : 2 ^ 9 * 2 ^ (e0 w) ≤ 2 ^ e := by
          rw [← pow_add, add_comm]
          exact Nat.pow_le_pow_right (by norm_num) he9
        have hbig : 512 * x ≤ t := by
          calc 512 * x ≤ 512 * (2 ^ (e0 w) * w) := Nat.mul_le_mul_left 512 he0_spec
            _ = (2 ^ 9 * 2 ^ (e0 w)) * w := by ring
            _ ≤ 2 ^ e * w := Nat.mul_le_mul_right w hpow9
            _ = t := hmul
        change t ≤ 256 * x at htn
        nlinarith
      rw [Finset.mem_coe, Finset.mem_product, mem_oddSmooth_iff, Finset.mem_range]
      exact ⟨⟨⟨hw1, hwn⟩, hwodd, hwsm⟩, he_lt⟩
    · intro t₁ ht₁ t₂ ht₂ hgeq
      rw [Finset.mem_coe] at ht₁ ht₂
      change t₁ ∈ (Finset.Icc x n).filter isSmooth256 at ht₁
      change t₂ ∈ (Finset.Icc x n).filter isSmooth256 at ht₂
      rw [Finset.mem_filter, Finset.mem_Icc] at ht₁ ht₂
      obtain ⟨hmul₁, _, hw1₁⟩ := two_pow_mul_odd_part (by omega : 1 ≤ t₁)
      obtain ⟨hmul₂, _, hw1₂⟩ := two_pow_mul_odd_part (by omega : 1 ≤ t₂)
      set e₁ := t₁.factorization 2
      set w₁ := t₁ / 2 ^ e₁
      set e₂ := t₂.factorization 2
      set w₂ := t₂ / 2 ^ e₂
      have he₁_ge : e0 w₁ ≤ e₁ := by
        dsimp only [e0]
        rw [dif_pos hw1₁]
        exact Nat.find_min' _ (by linarith [ht₁.1.1])
      have he₂_ge : e0 w₂ ≤ e₂ := by
        dsimp only [e0]
        rw [dif_pos hw1₂]
        exact Nat.find_min' _ (by linarith [ht₂.1.1])
      change (w₁, e₁ - e0 w₁) = (w₂, e₂ - e0 w₂) at hgeq
      injection hgeq with hw_eq hdiff_eq
      have he_eq : e₁ = e₂ := by
        have h_e0_eq : e0 w₁ = e0 w₂ := congr_arg e0 hw_eq
        omega
      calc t₁ = 2 ^ e₁ * w₁ := hmul₁.symm
        _ = 2 ^ e₂ * w₂ := by rw [he_eq, hw_eq]
        _ = t₂ := hmul₂
  calc ((Finset.Icc 1 n).filter (· ∈ B)).card
      ≤ S.card := Finset.card_le_card hsub
    _ ≤ (oddSmooth n ×ˢ Finset.range 9).card := hS_le
    _ = 9 * (oddSmooth n).card := by simp [mul_comm]

/-- Coprime count in `range (K * Q)` equals `K * Nat.totient Q`. -/
lemma card_coprime_range_mul (Q K : ℕ) :
    ((Finset.range (K * Q)).filter (fun u => Nat.Coprime u Q)).card = K * Nat.totient Q := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hsplit : Finset.range ((K + 1) * Q) =
        Finset.range (K * Q) ∪ Finset.Ico (K * Q) ((K + 1) * Q) := by
      ext u
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
      have : K * Q ≤ (K + 1) * Q := by nlinarith
      omega
    have hdisj : Disjoint (Finset.range (K * Q)) (Finset.Ico (K * Q) ((K + 1) * Q)) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rw [Finset.mem_range] at hu1
      rw [Finset.mem_Ico] at hu2
      omega
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint (Disjoint.mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj), ih]
    have hblock : ((Finset.Ico (K * Q) ((K + 1) * Q)).filter (fun u => Nat.Coprime u Q)).card =
        Nat.totient Q := by
      rw [Nat.totient_eq_card_coprime Q]
      symm
      apply Finset.card_bij (fun r _ => K * Q + r)
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨by omega, by linarith [show (K + 1) * Q = K * Q + Q by ring]⟩, ?_⟩
        rw [Nat.coprime_mul_right_add_left]
        exact hr.2.symm
      · intro r₁ _ r₂ _ heq
        omega
      · intro u hu
        rw [Finset.mem_filter, Finset.mem_Ico] at hu
        refine ⟨u - K * Q, ?_, by omega⟩
        rw [Finset.mem_filter, Finset.mem_range]
        have hu_lt : u < K * Q + Q := by linarith [show (K + 1) * Q = K * Q + Q by ring, hu.1.2]
        refine ⟨by omega, ?_⟩
        have hu_eq : K * Q + (u - K * Q) = u := by omega
        have hcop_u : Nat.Coprime (K * Q + (u - K * Q)) Q := hu_eq.symm ▸ hu.2
        rw [Nat.coprime_mul_right_add_left] at hcop_u
        exact hcop_u.symm
    rw [hblock]
    ring

/-- Exact coprime count in `[1, K * Q]` for `Q > 0`: equals `K * Nat.totient Q`. -/
lemma card_coprime_mul_period {Q : ℕ} (hQ : 0 < Q) (K : ℕ) :
    ((Finset.Icc 1 (K * Q)).filter (fun u => Nat.Coprime u Q)).card = K * Nat.totient Q := by
  have hshift : ((Finset.Icc 1 (K * Q)).filter (fun u => Nat.Coprime u Q)).card =
      ((Finset.range (K * Q)).filter (fun u => Nat.Coprime u Q)).card := by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp
    by_cases hQ1 : Q = 1
    · subst hQ1
      simp
    · have h0 : ¬ Nat.Coprime 0 Q := by
        rw [Nat.coprime_zero_left]
        omega
      have hKQ : ¬ Nat.Coprime (K * Q) Q := by
        intro hc
        have hdvd : Q ∣ Nat.gcd (K * Q) Q := dvd_gcd (dvd_mul_left Q K) dvd_rfl
        rw [hc.gcd_eq_one] at hdvd
        have : Q ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
        omega
      congr 1
      ext u
      rw [Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨⟨hu1, hule⟩, hcop⟩
        have hne : u ≠ K * Q := fun heq => hKQ (heq ▸ hcop)
        exact ⟨by omega, hcop⟩
      · rintro ⟨hult, hcop⟩
        have hne0 : u ≠ 0 := fun heq => h0 (heq ▸ hcop)
        exact ⟨⟨by omega, by omega⟩, hcop⟩
  rw [hshift, card_coprime_range_mul Q K]

/-- Lower bound at `m = (2 * n)! * Q256`:
`O(x) * m * phiQ256 < |B ∩ [1, m]| * (2 * x * Q256)`. -/
lemma lower_bound_at_m {N : ℕ} (hN : 8 ≤ N) :
    let x := 2 ^ N
    let A := (Finset.Ico x (2 * x)).filter isSmooth256
    let n := 256 * x
    let m := (2 * n).factorial * Q256
    let B := {k ≥ 1 | ∃ a ∈ A, a ∣ k}
    (oddSmooth x).card * m * phiQ256 <
      ((Finset.Icc 1 m).filter (· ∈ B)).card * (2 * x * Q256) := by
  intro x A n m B
  have hx_ge : 256 ≤ x := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  have hex_ew : ∀ w : ℕ, 1 ≤ w → ∃ e : ℕ, x ≤ 2 ^ e * w := by
    intro w hw
    exact ⟨N, by change x ≤ x * w; nlinarith⟩
  let ew : ℕ → ℕ := fun w => if hw : 1 ≤ w then Nat.find (hex_ew w hw) else 0
  let aw : ℕ → ℕ := fun w => 2 ^ (ew w) * w
  have haw_props : ∀ w ∈ oddSmooth x,
      x ≤ aw w ∧ aw w < 2 * x ∧ aw w ∈ A ∧ (aw w * Q256 ∣ m) := by
    intro w hw
    rw [mem_oddSmooth_iff] at hw
    rcases hw with ⟨⟨hw1, hwx⟩, hwodd, hwsm⟩
    have hspec : x ≤ aw w := by
      dsimp only [aw, ew]
      rw [dif_pos hw1]
      exact Nat.find_spec (hex_ew w hw1)
    have hew_pos : 1 ≤ ew w := by
      dsimp only [ew]
      rw [dif_pos hw1]
      by_contra h0
      have heq0 : Nat.find (hex_ew w hw1) = 0 := by omega
      have hspec0 : x ≤ 2 ^ 0 * w := heq0 ▸ Nat.find_spec (hex_ew w hw1)
      rw [pow_zero, one_mul] at hspec0
      have hwx_eq : w = x := le_antisymm hwx hspec0
      have hx_even : x % 2 = 0 := by
        dsimp only [x]
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0) with ⟨k, rfl⟩
        rw [pow_succ]
        omega
      omega
    have hlt2x : aw w < 2 * x := by
      have hmin : ¬ (x ≤ 2 ^ (ew w - 1) * w) := by
        have hew_eq : ew w = Nat.find (hex_ew w hw1) := dif_pos hw1
        have hlt_ew : ew w - 1 < Nat.find (hex_ew w hw1) := by omega
        exact Nat.find_min (hex_ew w hw1) hlt_ew
      have hmin' : 2 ^ (ew w - 1) * w < x := by omega
      have hmul2 : aw w = 2 * (2 ^ (ew w - 1) * w) := by
        dsimp only [aw]
        conv_lhs => rw [show ew w = (ew w - 1) + 1 by omega, pow_succ']
        ring
      linarith
    have haw_sm : isSmooth256 (aw w) := by
      refine ⟨by omega, fun p hp hdvd => ?_⟩
      rcases hp.dvd_mul.mp hdvd with hp2 | hpw
      · have := hp.dvd_of_dvd_pow hp2
        have := Nat.le_of_dvd (by norm_num) this
        omega
      · exact hwsm.2 p hp hpw
    have haw_mem : aw w ∈ A := by
      change aw w ∈ (Finset.Ico x (2 * x)).filter isSmooth256
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hspec, hlt2x⟩, haw_sm⟩
    have hdvd_fact : aw w ∣ (2 * n).factorial :=
      Nat.dvd_factorial (by omega) (by dsimp only [n]; omega)
    exact ⟨hspec, hlt2x, haw_mem, mul_dvd_mul_right hdvd_fact Q256⟩

  let Tw : ℕ → Finset ℕ := fun w =>
    ((Finset.Icc 1 (m / aw w)).filter (fun u => Nat.Coprime u Q256)).image (fun u => aw w * u)

  have hTw_sub : ∀ w ∈ oddSmooth x, Tw w ⊆ (Finset.Icc 1 m).filter (· ∈ B) := by
    intro w hw t ht
    obtain ⟨hx_le, _, haw_A, _⟩ := haw_props w hw
    simp only [Tw, Finset.mem_image] at ht
    rcases ht with ⟨u, hu, rfl⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hu
    rcases hu with ⟨⟨hu1, hum⟩, _⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    have ht1 : 1 ≤ aw w * u := by nlinarith
    have htm : aw w * u ≤ m := by
      calc aw w * u ≤ aw w * (m / aw w) := Nat.mul_le_mul_left _ hum
        _ ≤ m := Nat.mul_div_le m (aw w)
    exact ⟨⟨ht1, htm⟩, ht1, aw w, haw_A, dvd_mul_right (aw w) u⟩

  have hTw_disj : (oddSmooth x : Set ℕ).PairwiseDisjoint Tw := by
    intro w₁ hw₁ w₂ hw₂ hne
    change Disjoint (Tw w₁) (Tw w₂)
    rw [Finset.disjoint_left]
    intro t ht₁ ht₂
    simp only [Tw, Finset.mem_image] at ht₁ ht₂
    rcases ht₁ with ⟨u₁, hu₁, rfl⟩
    rcases ht₂ with ⟨u₂, hu₂, heq⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hu₁ hu₂
    rcases hu₁ with ⟨⟨hu₁1, _⟩, hcop₁⟩
    rcases hu₂ with ⟨⟨hu₂1, _⟩, hcop₂⟩
    rw [Finset.mem_coe, mem_oddSmooth_iff] at hw₁ hw₂
    rcases hw₁ with ⟨⟨hw₁_ge1, _⟩, hw₁_odd, hw₁_sm⟩
    rcases hw₂ with ⟨⟨hw₂_ge1, _⟩, hw₂_odd, hw₂_sm⟩
    have hw₁0 : w₁ ≠ 0 := by omega
    have hw₂0 : w₂ ≠ 0 := by omega
    have hu₁0 : u₁ ≠ 0 := by omega
    have hu₂0 : u₂ ≠ 0 := by omega
    have hweq : w₁ = w₂ := by
      apply Nat.factorization_inj hw₁0 hw₂0
      ext p
      by_cases hp : Nat.Prime p
      · by_cases hp2 : p = 2
        · subst hp2
          have hnd1 : ¬ (2 ∣ w₁) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
          have hnd2 : ¬ (2 ∣ w₂) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
          rw [Nat.factorization_eq_zero_of_not_dvd hnd1, Nat.factorization_eq_zero_of_not_dvd hnd2]
        · by_cases hple : p ≤ 256
          · have hp_mem : p ∈ oddPrimes256 := prime_le_256_mem p hp hple hp2
            have hp_dvd_Q : p ∣ Q256 := by rw [Q256_def]; exact List.dvd_prod hp_mem
            have hnd_u1 : ¬ (p ∣ u₁) := by
              intro hpu
              have hcop_p : Nat.Coprime u₁ p := Nat.Coprime.coprime_dvd_right hp_dvd_Q hcop₁
              exact hp.not_dvd_one (hcop_p.gcd_eq_one ▸ dvd_gcd hpu dvd_rfl)
            have hnd_u2 : ¬ (p ∣ u₂) := by
              intro hpu
              have hcop_p : Nat.Coprime u₂ p := Nat.Coprime.coprime_dvd_right hp_dvd_Q hcop₂
              exact hp.not_dvd_one (hcop_p.gcd_eq_one ▸ dvd_gcd hpu dvd_rfl)
            have hnd_2pow1 : ¬ (p ∣ 2 ^ (ew w₁)) := by
              intro hd
              have := hp.dvd_of_dvd_pow hd
              have := Nat.le_of_dvd (by norm_num) this
              have := hp.two_le
              omega
            have hnd_2pow2 : ¬ (p ∣ 2 ^ (ew w₂)) := by
              intro hd
              have := hp.dvd_of_dvd_pow hd
              have := Nat.le_of_dvd (by norm_num) this
              have := hp.two_le
              omega
            have hf_eq : (aw w₁ * u₁).factorization p = (aw w₂ * u₂).factorization p := by
              rw [heq]
            dsimp only [aw] at hf_eq
            have h2pos1 : (2 ^ ew w₁ : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.one_le_pow _ 2 (by norm_num))
            have h2pos2 : (2 ^ ew w₂ : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.one_le_pow _ 2 (by norm_num))
            rw [Nat.factorization_mul (mul_ne_zero h2pos1 hw₁0) hu₁0,
                Nat.factorization_mul h2pos1 hw₁0,
                Nat.factorization_mul (mul_ne_zero h2pos2 hw₂0) hu₂0,
                Nat.factorization_mul h2pos2 hw₂0] at hf_eq
            simp only [Finsupp.coe_add, Pi.add_apply,
              Nat.factorization_eq_zero_of_not_dvd hnd_u1,
              Nat.factorization_eq_zero_of_not_dvd hnd_u2,
              Nat.factorization_eq_zero_of_not_dvd hnd_2pow1,
              Nat.factorization_eq_zero_of_not_dvd hnd_2pow2, zero_add, add_zero] at hf_eq
            exact hf_eq
          · have hnd1 : ¬ (p ∣ w₁) := fun hd => hple (hw₁_sm.2 p hp hd)
            have hnd2 : ¬ (p ∣ w₂) := fun hd => hple (hw₂_sm.2 p hp hd)
            rw [Nat.factorization_eq_zero_of_not_dvd hnd1, Nat.factorization_eq_zero_of_not_dvd hnd2]
      · rw [Nat.factorization_eq_zero_of_not_prime w₁ hp,
            Nat.factorization_eq_zero_of_not_prime w₂ hp]
    exact hne hweq

  have hTw_card : ∀ w ∈ oddSmooth x, m * phiQ256 < (Tw w).card * (2 * x * Q256) := by
    intro w hw
    obtain ⟨hx_le, hlt2x, _, hdvd_m⟩ := haw_props w hw
    have haw_pos : 0 < aw w := by omega
    rcases hdvd_m with ⟨Kw, hm_eq⟩
    have hm_div : m / aw w = Kw * Q256 := by
      have : m = aw w * (Kw * Q256) := by linarith
      rw [this, Nat.mul_div_cancel_left _ haw_pos]
    have hcard_eq : (Tw w).card = Kw * phiQ256 := by
      dsimp only [Tw]
      rw [Finset.card_image_of_injective _ (fun u₁ u₂ h => Nat.eq_of_mul_eq_mul_left haw_pos h),
          hm_div, card_coprime_mul_period Q256_pos Kw, totient_Q256]
    have hKw_pos : 0 < Kw := by
      have hm_pos : 0 < m := Nat.mul_pos (Nat.factorial_pos _) Q256_pos
      by_contra h0
      have : Kw = 0 := by omega
      rw [this, mul_zero] at hm_eq
      omega
    have hprod_pos : 0 < Kw * Q256 * phiQ256 :=
      Nat.mul_pos (Nat.mul_pos hKw_pos Q256_pos) phiQ256_pos
    rw [hcard_eq, hm_eq]
    calc (aw w * Q256 * Kw) * phiQ256
        = aw w * (Kw * Q256 * phiQ256) := by ring
      _ < (2 * x) * (Kw * Q256 * phiQ256) :=
          Nat.mul_lt_mul_of_pos_right hlt2x hprod_pos
      _ = (Kw * phiQ256) * (2 * x * Q256) := by ring

  have hO_nonempty : (oddSmooth x).Nonempty := ⟨1, one_mem_oddSmooth (by omega)⟩
  have hsum_lt : ∑ w ∈ oddSmooth x, (m * phiQ256) <
      ∑ w ∈ oddSmooth x, (Tw w).card * (2 * x * Q256) :=
    Finset.sum_lt_sum_of_nonempty hO_nonempty hTw_card
  rw [Finset.sum_const, smul_eq_mul, ← Finset.sum_mul, ← Finset.card_biUnion hTw_disj] at hsum_lt
  have hbiU_sub : (oddSmooth x).biUnion Tw ⊆ (Finset.Icc 1 m).filter (· ∈ B) := by
    intro t ht
    rcases Finset.mem_biUnion.mp ht with ⟨w, hw, htw⟩
    exact hTw_sub w hw htw
  have hcard_le : ((oddSmooth x).biUnion Tw).card ≤ ((Finset.Icc 1 m).filter (· ∈ B)).card :=
    Finset.card_le_card hbiU_sub
  calc (oddSmooth x).card * m * phiQ256
      = (oddSmooth x).card * (m * phiQ256) := by ring
    _ < ((oddSmooth x).biUnion Tw).card * (2 * x * Q256) := hsum_lt
    _ ≤ ((Finset.Icc 1 m).filter (· ∈ B)).card * (2 * x * Q256) :=
        Nat.mul_le_mul_right _ hcard_le

/-- **Main Theorem (Complete Formal Disproof of Erdős Problem 488):**
The universal inequality in `Erdos488Prop` is false. -/
theorem counterexample : ¬ (type_of% @Erdos488.erdos_488) := by
  intro hErdos
  obtain ⟨j, hj1, _, hscale⟩ := exists_good_scale
  let N := 8 * j
  have hN : 8 ≤ N := by dsimp only [N]; omega
  let x := 2 ^ N
  have hx_ge : 256 ≤ x := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  let A := (Finset.Ico x (2 * x)).filter isSmooth256
  let n := 256 * x
  let m := (2 * n).factorial * Q256
  let B := {k ≥ 1 | ∃ a ∈ A, a ∣ k}

  have hx_smooth : isSmooth256 x := by
    refine ⟨by omega, fun p hp hdvd => ?_⟩
    have := hp.dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hx_mem : x ∈ A := by
    change x ∈ (Finset.Ico x (2 * x)).filter isSmooth256
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨le_rfl, by omega⟩, hx_smooth⟩
  have hA_nonempty : A.Nonempty := ⟨x, hx_mem⟩
  have h0_not_mem : 0 ∉ A := by
    change 0 ∉ (Finset.Ico x (2 * x)).filter isSmooth256
    rw [Finset.mem_filter, Finset.mem_Ico]
    omega
  have h1_not_mem : 1 ∉ A := by
    change 1 ∉ (Finset.Ico x (2 * x)).filter isSmooth256
    rw [Finset.mem_filter, Finset.mem_Ico]
    omega
  have hmax_le : A.max ≤ n := by
    rw [Finset.max_le_iff]
    intro a ha
    change a ∈ (Finset.Ico x (2 * x)).filter isSmooth256 at ha
    rw [Finset.mem_filter, Finset.mem_Ico] at ha
    have : a ≤ n := by dsimp only [n]; omega
    exact WithBot.coe_le_coe.mpr this
  have hn_pos : 0 < n := by dsimp only [n]; omega
  have hnm : m > n := by
    have hfact : 2 * n ≤ (2 * n).factorial := Nat.self_le_factorial (2 * n)
    have hQ1 : 1 ≤ Q256 := Q256_pos
    calc n < 2 * n := by omega
      _ ≤ (2 * n).factorial := hfact
      _ = (2 * n).factorial * 1 := (mul_one _).symm
      _ ≤ (2 * n).factorial * Q256 := Nat.mul_le_mul_left _ hQ1

  set fn := ((Finset.Icc 1 n).filter (· ∈ B)).card
  set fm := ((Finset.Icc 1 m).filter (· ∈ B)).card
  set Ox := (oddSmooth x).card
  set On := (oddSmooth n).card

  have hub : fn ≤ 9 * On := upper_bound_at_n (by omega : 2 ≤ x)
  have hscale' : 5 * On ≤ 6 * Ox := by
    have hnx : n = 2 ^ (8 * (j + 1)) := by
      dsimp only [n, x, N]
      rw [show 8 * (j + 1) = 8 + 8 * j by ring, pow_add]
      norm_num
    simpa only [On, Ox, x, N, hnx] using hscale
  have h5fn : 5 * fn ≤ 54 * Ox := by linarith
  have hlb : Ox * m * phiQ256 < fm * (2 * x * Q256) := lower_bound_at_m hN
  have hOx_pos : 0 < Ox := Finset.card_pos.mpr ⟨1, one_mem_oddSmooth (by omega)⟩
  have hm_pos : 0 < m := by omega
  have hx_pos : 0 < x := by omega
  have hQ_pos : 0 < Q256 := Q256_pos
  have htot := key_totient_ineq

  have hnat_contra : 2 * fn * m < fm * n := by
    have hmxOx : 0 < m * x * Ox * Ox :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hm_pos hx_pos) hOx_pos) hOx_pos
    have h5nOx : 0 < 5 * n * Ox :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) hn_pos) hOx_pos
    have hmul : (2 * fn * m) * (10 * x * Q256 * Ox) < (fm * n) * (10 * x * Q256 * Ox) := by
      calc (2 * fn * m) * (10 * x * Q256 * Ox)
          = (5 * fn) * (4 * m * x * Q256 * Ox) := by ring
        _ ≤ (54 * Ox) * (4 * m * x * Q256 * Ox) :=
            Nat.mul_le_mul_right _ h5fn
        _ = (216 * Q256) * (m * x * Ox * Ox) := by ring
        _ < (1280 * phiQ256) * (m * x * Ox * Ox) :=
            Nat.mul_lt_mul_of_pos_right htot hmxOx
        _ = (5 * (256 * x) * Ox) * (Ox * m * phiQ256) := by ring
        _ < (5 * n * Ox) * (fm * (2 * x * Q256)) := by
            dsimp only [n]
            exact Nat.mul_lt_mul_of_pos_left hlb h5nOx
        _ = (fm * n) * (10 * x * Q256 * Ox) := by ring
    exact Nat.lt_of_mul_lt_mul_right hmul

  have hclaim := hErdos A hA_nonempty h0_not_mem h1_not_mem n m hnm hmax_le
  have hn_qpos : (0 : ℚ) < n := by exact_mod_cast hn_pos
  have hm_qpos : (0 : ℚ) < m := by exact_mod_cast hm_pos
  rw [div_lt_div_iff₀ hm_qpos hn_qpos] at hclaim
  have hnat_claim : fm * n < 2 * fn * m := by exact_mod_cast hclaim
  omega

end OMA.Erdos488Port


theorem OMA.disproof : ¬ (type_of% @Erdos488.erdos_488) :=
  OMA.Erdos488Port.counterexample

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS
-/
