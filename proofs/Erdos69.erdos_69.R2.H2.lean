import OMAReductions.R_Erdos69_erdos_69_R2

/-!
Unified CRT moment proof for `OMA.R_Erdos69_erdos_69_R2.H2`.
We expand the first, second, and fourth moments of `W i = ∑ p ∈ P, X p i`
into prime-tuple sums, reduce each tuple to a product over distinct primes
using `InjOn (· % p) J`, and count simultaneous congruences via the Chinese
Remainder Theorem.
-/

open Finset

private lemma mod_eq_of_dvd_add_le {p a r₁ r₂ : ℕ} (hp : 0 < p) (hle : r₁ ≤ r₂)
    (h₁ : p ∣ a + r₁) (h₂ : p ∣ a + r₂) : r₁ % p = r₂ % p := by
  rcases h₁ with ⟨k₁, hk₁⟩
  rcases h₂ with ⟨k₂, hk₂⟩
  have hkle : k₁ ≤ k₂ := Nat.le_of_mul_le_mul_left (by omega) hp
  have hr₂ : r₂ = r₁ + p * (k₂ - k₁) := by
    have hmul : p * (k₂ - k₁) = p * k₂ - p * k₁ := Nat.mul_sub p k₂ k₁
    omega
  rw [hr₂, Nat.add_mul_mod_self_left]

private lemma mod_eq_of_dvd_add {p a r₁ r₂ : ℕ} (hp : 0 < p)
    (h₁ : p ∣ a + r₁) (h₂ : p ∣ a + r₂) : r₁ % p = r₂ % p := by
  rcases le_total r₁ r₂ with h | h
  · exact mod_eq_of_dvd_add_le hp h h₁ h₂
  · exact (mod_eq_of_dvd_add_le hp h h₂ h₁).symm

private lemma sum_ite_pow {J : Finset ℕ} {P : ℕ → Prop} [DecidablePred P] {w : ℕ → ℝ}
    (huniq : ∀ r₁ ∈ J, ∀ r₂ ∈ J, P r₁ → P r₂ → r₁ = r₂) {k : ℕ} (hk : k ≠ 0) :
    (∑ r ∈ J, if P r then w r else 0) ^ k = ∑ r ∈ J, if P r then (w r) ^ k else 0 := by
  by_cases h : ∃ r₀ ∈ J, P r₀
  · rcases h with ⟨r₀, hr₀J, hr₀P⟩
    have heq : ∀ f : ℕ → ℝ, (∑ r ∈ J, if P r then f r else 0) = f r₀ := fun f => by
      rw [Finset.sum_eq_single r₀]
      · simp [hr₀P]
      · intro r hrJ hne
        have hnot : ¬ P r := fun hPr => hne (huniq r hrJ r₀ hr₀J hPr hr₀P)
        simp [hnot]
      · intro hnot; exact absurd hr₀J hnot
    rw [heq w, heq (fun r => (w r) ^ k)]
  · push Not at h
    have h1 : (∑ r ∈ J, if P r then w r else 0) = 0 :=
      Finset.sum_eq_zero fun r hr => if_neg (h r hr)
    have h2 : (∑ r ∈ J, if P r then (w r) ^ k else 0) = 0 :=
      Finset.sum_eq_zero fun r hr => if_neg (h r hr)
    rw [h1, h2, zero_pow hk]

private lemma card_filter_mod_sub_div_le_one {Q M c : ℕ} (hQ : 0 < Q) (hc : c < Q) :
    |(((Finset.range M).filter (fun i => i % Q = c)).card : ℝ) - (M : ℝ) / (Q : ℝ)| ≤ 1 := by
  set q := M / Q
  set rem := M % Q
  have hdiv : Q * q + rem = M := Nat.div_add_mod M Q
  have hrem : rem < Q := Nat.mod_lt M hQ
  have hQpos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hMdiv : (M : ℝ) / (Q : ℝ) = (q : ℝ) + (rem : ℝ) / (Q : ℝ) := by
    have hMcast : (M : ℝ) = (Q : ℝ) * (q : ℝ) + (rem : ℝ) := by exact_mod_cast hdiv.symm
    rw [hMcast, add_div, mul_div_cancel_left₀ _ hQpos.ne']
  have hfrac_nonneg : 0 ≤ (rem : ℝ) / (Q : ℝ) := by positivity
  have hfrac_le : (rem : ℝ) / (Q : ℝ) ≤ 1 := (div_le_one hQpos).mpr (by exact_mod_cast hrem.le)
  have hinj : Function.Injective (fun k : ℕ => Q * k + c) :=
    fun k₁ k₂ h => Nat.eq_of_mul_eq_mul_left hQ (Nat.add_right_cancel h)
  by_cases hcr : c < rem
  · have hset : (Finset.range M).filter (fun i => i % Q = c) =
        (Finset.range (q + 1)).image (fun k => Q * k + c) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hiM, himod⟩
        refine ⟨i / Q, ?_, ?_⟩
        · by_contra hge
          push Not at hge
          have h1 : Q * (q + 1) ≤ Q * (i / Q) := Nat.mul_le_mul_left Q hge
          have h2 : Q * (i / Q) + i % Q = i := Nat.div_add_mod i Q
          rw [mul_add, mul_one] at h1
          omega
        · rw [← himod]; exact Nat.div_add_mod i Q
      · rintro ⟨k, hk, rfl⟩
        refine ⟨?_, ?_⟩
        · have h1 : Q * k ≤ Q * q := Nat.mul_le_mul_left Q (Nat.lt_succ_iff.mp hk)
          omega
        · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_range,
      Nat.cast_add, Nat.cast_one, hMdiv, abs_le]
    constructor <;> linarith
  · have hset : (Finset.range M).filter (fun i => i % Q = c) =
        (Finset.range q).image (fun k => Q * k + c) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hiM, himod⟩
        refine ⟨i / Q, ?_, ?_⟩
        · by_contra hge
          push Not at hge
          have h1 : Q * q ≤ Q * (i / Q) := Nat.mul_le_mul_left Q hge
          have h2 : Q * (i / Q) + i % Q = i := Nat.div_add_mod i Q
          omega
        · rw [← himod]; exact Nat.div_add_mod i Q
      · rintro ⟨k, hk, rfl⟩
        refine ⟨?_, ?_⟩
        · have h1 : Q * (k + 1) ≤ Q * q := Nat.mul_le_mul_left Q hk
          rw [mul_add, mul_one] at h1
          omega
        · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc]
    rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_range, hMdiv, abs_le]
    constructor <;> linarith

private lemma single_prime_cong {p D b r : ℕ} (hp : Nat.Prime p) (hpD : p.Coprime D) :
    ∃ c < p, ∀ i : ℕ, p ∣ D * i + b + r ↔ i % p = c := by
  have : Fact p.Prime := ⟨hp⟩
  have hD0 : (D : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ D := (ZMod.natCast_eq_zero_iff D p).mp h
    exact hp.not_dvd_one (hpD.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hdvd)
  let x : ZMod p := -((b : ZMod p) + (r : ZMod p)) * (D : ZMod p)⁻¹
  refine ⟨x.val, ZMod.val_lt x, fun i => ?_⟩
  have hx : (D : ZMod p) * x + (b : ZMod p) + (r : ZMod p) = 0 := by
    dsimp only [x]
    rw [mul_comm _ (D : ZMod p)⁻¹, ← mul_assoc, mul_inv_cancel₀ hD0, one_mul]
    ring
  calc p ∣ D * i + b + r
    _ ↔ ((D * i + b + r : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).symm
    _ ↔ (D : ZMod p) * (i : ZMod p) + (b : ZMod p) + (r : ZMod p) = 0 := by push_cast; rfl
    _ ↔ (D : ZMod p) * (i : ZMod p) = (D : ZMod p) * x := by
        constructor
        · intro h; linear_combination h - hx
        · intro h; linear_combination h + hx
    _ ↔ (i : ZMod p) = x := ⟨mul_left_cancel₀ hD0, fun h => by rw [h]⟩
    _ ↔ (i : ZMod p) = (x.val : ZMod p) := by rw [ZMod.natCast_zmod_val]
    _ ↔ i ≡ x.val [MOD p] := ZMod.natCast_eq_natCast_iff _ _ _
    _ ↔ i % p = x.val := by rw [Nat.ModEq, Nat.mod_eq_of_lt (ZMod.val_lt x)]

private lemma crt_finset_cong {S : Finset ℕ} {D b : ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p ∧ p.Coprime D) (ρ : ℕ → ℕ) :
    0 < ∏ p ∈ S, p ∧ ∃ c < ∏ p ∈ S, p,
      ∀ i : ℕ, (∀ p ∈ S, p ∣ D * i + b + ρ p) ↔ i % (∏ p ∈ S, p) = c := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨by simp, 0, by simp, fun i => by simp [Nat.mod_one]⟩
  | @insert p s hp ih =>
    have hp_prime : Nat.Prime p := (hS p (Finset.mem_insert_self p s)).1
    have hp_cop : p.Coprime D := (hS p (Finset.mem_insert_self p s)).2
    have hs : ∀ q ∈ s, Nat.Prime q ∧ q.Coprime D :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨hQ_pos, c_s, hc_s_lt, hc_s⟩ := ih hs
    obtain ⟨c_p, hc_p_lt, hc_p⟩ := single_prime_cong hp_prime hp_cop (b := b) (r := ρ p)
    have hcop : p.Coprime (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq =>
        (Nat.coprime_primes hp_prime (hs q hq).1).mpr (fun heq => hp (heq ▸ hq))
    have hQ'_pos : 0 < p * ∏ q ∈ s, q := Nat.mul_pos hp_prime.pos hQ_pos
    let k := (Nat.chineseRemainder hcop c_p c_s).val
    have hk_p : k ≡ c_p [MOD p] := (Nat.chineseRemainder hcop c_p c_s).property.1
    have hk_s : k ≡ c_s [MOD ∏ q ∈ s, q] := (Nat.chineseRemainder hcop c_p c_s).property.2
    let c := k % (p * ∏ q ∈ s, q)
    have hc_lt : c < p * ∏ q ∈ s, q := Nat.mod_lt k hQ'_pos
    have hc_mod_p : c % p = c_p := by
      dsimp only [c]
      rw [Nat.mod_mul_right_mod, hk_p, Nat.mod_eq_of_lt hc_p_lt]
    have hc_mod_s : c % (∏ q ∈ s, q) = c_s := by
      dsimp only [c]
      rw [Nat.mod_mul_left_mod, hk_s, Nat.mod_eq_of_lt hc_s_lt]
    rw [Finset.prod_insert hp]
    refine ⟨hQ'_pos, c, hc_lt, fun i => ?_⟩
    calc (∀ q ∈ insert p s, q ∣ D * i + b + ρ q)
      _ ↔ p ∣ D * i + b + ρ p ∧ ∀ q ∈ s, q ∣ D * i + b + ρ q := by
          simp only [Finset.mem_insert, forall_eq_or_imp]
      _ ↔ i % p = c_p ∧ i % (∏ q ∈ s, q) = c_s := by rw [hc_p, hc_s]
      _ ↔ i ≡ c [MOD p] ∧ i ≡ c [MOD ∏ q ∈ s, q] := by
          simp only [Nat.ModEq, hc_mod_p, hc_mod_s]
      _ ↔ i ≡ c [MOD p * ∏ q ∈ s, q] := Nat.modEq_and_modEq_iff_modEq_mul hcop
      _ ↔ i % (p * ∏ q ∈ s, q) = c := by rw [Nat.ModEq, Nat.mod_eq_of_lt hc_lt]

private lemma sum_pow_le_pow_sum {J : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ r ∈ J, 0 ≤ a r) :
    ∀ {m : ℕ}, m ≠ 0 → ∑ r ∈ J, (a r) ^ m ≤ (∑ r ∈ J, a r) ^ m := by
  intro m hm
  rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨k, rfl⟩
  clear hm
  induction k with
  | zero => simp
  | succ k ih =>
    calc ∑ r ∈ J, (a r) ^ (k + 2)
      _ = ∑ r ∈ J, a r * (a r) ^ (k + 1) := by
          refine Finset.sum_congr rfl fun r _ => ?_; ring
      _ ≤ ∑ r ∈ J, (∑ r' ∈ J, a r') * (a r) ^ (k + 1) := by
          refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_right
            (Finset.single_le_sum ha hr) (pow_nonneg (ha r hr) _)
      _ = (∑ r' ∈ J, a r') * ∑ r ∈ J, (a r) ^ (k + 1) := by rw [Finset.mul_sum]
      _ ≤ (∑ r' ∈ J, a r') * (∑ r ∈ J, a r) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left ih (Finset.sum_nonneg ha)
      _ = (∑ r ∈ J, a r) ^ (k + 2) := by ring

private lemma prod_ite_zero_univ {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) :
    (∏ a : α, if P a then f a else 0) = if (∀ a : α, P a) then ∏ a : α, f a else 0 := by
  by_cases h : ∀ a : α, P a
  · rw [if_pos h]
    exact Finset.prod_congr rfl fun a _ => if_pos (h a)
  · rw [if_neg h]
    push Not at h
    rcases h with ⟨a₀, ha₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ a₀) (if_neg ha₀)

private lemma prod_finset_sum_eq_sum_fun (S J : Finset ℕ) (f : ℕ → ℕ → ℝ) :
    (∏ p ∈ S, ∑ r ∈ J, f p r) = ∑ ρ : S → J, ∏ p : S, f p.1 (ρ p).1 := by
  calc ∏ p ∈ S, ∑ r ∈ J, f p r
    _ = ∏ p : S, ∑ r ∈ J, f p.1 r := (Finset.prod_coe_sort S (fun p => ∑ r ∈ J, f p r)).symm
    _ = ∏ p : S, ∑ r : J, f p.1 r.1 :=
        Finset.prod_congr rfl fun p _ => (Finset.sum_coe_sort J (fun r => f p.1 r)).symm
    _ = ∑ ρ : S → J, ∏ p : S, f p.1 (ρ p).1 :=
        Fintype.prod_sum (fun (p : S) (r : J) => f p.1 r.1)

private lemma distinct_prime_moment {S J : Finset ℕ} {D b M : ℕ} {w : ℕ → ℝ} {e : ℕ → ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p ∧ p.Coprime D ∧ Set.InjOn (fun r : ℕ => r % p) (J : Set ℕ))
    (he : ∀ p ∈ S, e p ≠ 0) :
    let X (p i : ℕ) := ∑ r ∈ J, if p ∣ D * i + b + r then w r else 0
    |(∑ i ∈ Finset.range M, ∏ p ∈ S, (X p i) ^ (e p)) -
      (M : ℝ) / (∏ p ∈ S, (p : ℝ)) * (∏ p ∈ S, ∑ r ∈ J, (w r) ^ (e p))| ≤
      (∑ r ∈ J, |w r|) ^ (∑ p ∈ S, e p) := by
  classical
  intro X
  set Q : ℕ := ∏ p ∈ S, p
  have hQcast : (Q : ℝ) = ∏ p ∈ S, (p : ℝ) := by simp [Q]
  let val (ρ : S → J) : ℝ := ∏ p : S, (w (ρ p).1) ^ (e p.1)
  let cond (i : ℕ) (ρ : S → J) : Prop := ∀ p : S, p.1 ∣ D * i + b + (ρ p).1
  have hpow (i : ℕ) :
      ∏ p ∈ S, (X p i) ^ (e p) = ∑ ρ : S → J, if cond i ρ then val ρ else 0 := by
    have h1 : ∏ p ∈ S, (X p i) ^ (e p) =
        ∏ p ∈ S, ∑ r ∈ J, if p ∣ D * i + b + r then (w r) ^ (e p) else 0 := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have huniq : ∀ r₁ ∈ J, ∀ r₂ ∈ J, p ∣ D * i + b + r₁ → p ∣ D * i + b + r₂ → r₁ = r₂ :=
        fun r₁ hr₁ r₂ hr₂ hd₁ hd₂ =>
          (hS p hp).2.2 hr₁ hr₂ (mod_eq_of_dvd_add (hS p hp).1.pos hd₁ hd₂)
      exact sum_ite_pow huniq (he p hp)
    rw [h1, prod_finset_sum_eq_sum_fun S J
      (fun p r => if p ∣ D * i + b + r then (w r) ^ (e p) else 0)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    exact prod_ite_zero_univ (fun p : S => p.1 ∣ D * i + b + (ρ p).1)
      (fun p : S => (w (ρ p).1) ^ (e p.1))
  have hsum_eq :
      (∑ i ∈ Finset.range M, ∏ p ∈ S, (X p i) ^ (e p)) =
        ∑ ρ : S → J, ∑ i ∈ Finset.range M, if cond i ρ then val ρ else 0 := by
    simp_rw [hpow]
    exact Finset.sum_comm
  have hmain_eq :
      (M : ℝ) / (∏ p ∈ S, (p : ℝ)) * (∏ p ∈ S, ∑ r ∈ J, (w r) ^ (e p)) =
        ∑ ρ : S → J, (M : ℝ) / (Q : ℝ) * val ρ := by
    rw [← Finset.mul_sum, ← hQcast,
      prod_finset_sum_eq_sum_fun S J (fun p r => (w r) ^ (e p))]
  rw [hsum_eq, hmain_eq, ← Finset.sum_sub_distrib]
  have hterm (ρ : S → J) :
      |(∑ i ∈ Finset.range M, if cond i ρ then val ρ else 0) - (M : ℝ) / (Q : ℝ) * val ρ| ≤
        ∏ p : S, |w (ρ p).1| ^ (e p.1) := by
    let ρ' : ℕ → ℕ := fun p => if h : p ∈ S then (ρ ⟨p, h⟩).1 else 0
    obtain ⟨hQ_pos, c, hc_lt, hc⟩ :=
      crt_finset_cong (fun p hp => ⟨(hS p hp).1, (hS p hp).2.1⟩) ρ' (b := b)
    have hiff (i : ℕ) : cond i ρ ↔ i % Q = c := by
      rw [← hc i]
      constructor
      · intro h p hp
        simpa only [ρ', dif_pos hp] using h ⟨p, hp⟩
      · intro h ⟨p, hp⟩
        simpa only [ρ', dif_pos hp] using h p hp
    have hinner :
        (∑ i ∈ Finset.range M, if cond i ρ then val ρ else 0) =
        (((Finset.range M).filter (fun i => i % Q = c)).card : ℝ) * val ρ := by
      have : (∑ i ∈ Finset.range M, if cond i ρ then val ρ else 0) =
          ∑ i ∈ Finset.range M, if i % Q = c then val ρ else 0 :=
        Finset.sum_congr rfl fun i _ => by simp only [hiff i]
      rw [this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [hinner, ← sub_mul, abs_mul]
    have hcnt := card_filter_mod_sub_div_le_one (M := M) hQ_pos hc_lt
    have habs_val : |val ρ| = ∏ p : S, |w (ρ p).1| ^ (e p.1) := by
      dsimp only [val]
      rw [Finset.abs_prod]
      refine Finset.prod_congr rfl fun p _ => abs_pow _ _
    rw [habs_val]
    calc |(((Finset.range M).filter (fun i => i % Q = c)).card : ℝ) - (M : ℝ) / (Q : ℝ)| *
          ∏ p : S, |w (ρ p).1| ^ (e p.1)
      _ ≤ 1 * ∏ p : S, |w (ρ p).1| ^ (e p.1) :=
          mul_le_mul_of_nonneg_right hcnt (Finset.prod_nonneg fun p _ => by positivity)
      _ = ∏ p : S, |w (ρ p).1| ^ (e p.1) := one_mul _
  calc |∑ ρ : S → J, ((∑ i ∈ Finset.range M, if cond i ρ then val ρ else 0) -
          (M : ℝ) / (Q : ℝ) * val ρ)|
    _ ≤ ∑ ρ : S → J, |(∑ i ∈ Finset.range M, if cond i ρ then val ρ else 0) -
          (M : ℝ) / (Q : ℝ) * val ρ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ρ : S → J, ∏ p : S, |w (ρ p).1| ^ (e p.1) :=
        Finset.sum_le_sum fun ρ _ => hterm ρ
    _ = ∏ p ∈ S, ∑ r ∈ J, |w r| ^ (e p) :=
        (prod_finset_sum_eq_sum_fun S J (fun p r => |w r| ^ (e p))).symm
    _ ≤ ∏ p ∈ S, (∑ r ∈ J, |w r|) ^ (e p) :=
        Finset.prod_le_prod (fun p _ => Finset.sum_nonneg fun r _ => by positivity)
          (fun p hp => sum_pow_le_pow_sum (fun r _ => abs_nonneg _) (he p hp))
    _ = (∑ r ∈ J, |w r|) ^ (∑ p ∈ S, e p) := Finset.prod_pow_eq_pow_sum _ _ _

private lemma sum_count_toFinset (l : List ℕ) :
    ∑ p ∈ l.toFinset, l.count p = l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a ∈ t
    · have hset : (a :: t).toFinset = t.toFinset := by
        ext x; simp [ha]
      have hcnt : ∀ p, (a :: t).count p = t.count p + if p = a then 1 else 0 := fun p => by
        by_cases hpa : p = a
        · subst hpa; simp
        · simp [hpa, Ne.symm hpa]
      rw [hset]
      simp_rw [hcnt]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' _ a,
        if_pos (List.mem_toFinset.mpr ha), ih]
      simp
    · have hset : (a :: t).toFinset = insert a t.toFinset := by
        ext x; simp
      have ha' : a ∉ t.toFinset := by simpa using ha
      have ha_cnt : (a :: t).count a = 1 := by
        simp [List.count_eq_zero.mpr ha]
      have hother : ∑ p ∈ t.toFinset, (a :: t).count p = ∑ p ∈ t.toFinset, t.count p := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hne : p ≠ a := fun h => ha' (h ▸ hp)
        simp [Ne.symm hne]
      rw [hset, Finset.sum_insert ha', ha_cnt, hother, ih]
      simp [add_comm]

private lemma prod_pow_count_toFinset (l : List ℕ) (f : ℕ → ℝ) :
    ∏ p ∈ l.toFinset, (f p) ^ (l.count p) = (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a ∈ t
    · have hset : (a :: t).toFinset = t.toFinset := by
        ext x; simp [ha]
      have ha_mem : a ∈ t.toFinset := List.mem_toFinset.mpr ha
      rw [hset, ← Finset.mul_prod_erase t.toFinset (fun p => (f p) ^ ((a :: t).count p)) ha_mem]
      have herase : ∏ p ∈ t.toFinset.erase a, (f p) ^ ((a :: t).count p) =
          ∏ p ∈ t.toFinset.erase a, (f p) ^ (t.count p) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hne : p ≠ a := (Finset.mem_erase.mp hp).1
        simp [Ne.symm hne]
      have ha_cnt : (a :: t).count a = t.count a + 1 := by simp
      rw [herase, ha_cnt, pow_succ', mul_assoc,
        Finset.mul_prod_erase t.toFinset (fun p => (f p) ^ (t.count p)) ha_mem, ih]
      simp
    · have hset : (a :: t).toFinset = insert a t.toFinset := by
        ext x; simp
      have ha' : a ∉ t.toFinset := by simpa using ha
      have ha_cnt : (a :: t).count a = 1 := by
        simp [List.count_eq_zero.mpr ha]
      have hother : ∏ p ∈ t.toFinset, (f p) ^ ((a :: t).count p) =
          ∏ p ∈ t.toFinset, (f p) ^ (t.count p) := by
        refine Finset.prod_congr rfl fun p hp => ?_
        have hne : p ≠ a := fun h => ha' (h ▸ hp)
        simp [Ne.symm hne]
      rw [hset, Finset.prod_insert ha', ha_cnt, pow_one, hother, ih]
      simp

theorem OMA.solution : OMA.R_Erdos69_erdos_69_R2.H2 := by
  intro P J D b M w ⟨hP, hw0, hlo, hhi, h4, hM⟩
  let W (i : ℕ) : ℝ := ∑ r ∈ J, w r * (∑ p ∈ P, if p ∣ D * i + b + r then (1 : ℝ) else 0)
  let X (p i : ℕ) : ℝ := ∑ r ∈ J, if p ∣ D * i + b + r then w r else 0
  have hW_eq (i : ℕ) : W i = ∑ p ∈ P, X p i := by
    dsimp only [W, X]
    simp_rw [Finset.mul_sum, mul_ite, mul_one, mul_zero]
    exact Finset.sum_comm
  set A : ℝ := ∑ r ∈ J, |w r|
  set B : ℝ := (P.card : ℝ) * A
  have hA_nonneg : 0 ≤ A := Finset.sum_nonneg fun r _ => abs_nonneg _
  have hB_nonneg : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hA_nonneg
  have hM_nonneg : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have h1B4 : (1 + B) ^ 4 = 1 + 4 * B + 6 * B ^ 2 + 4 * B ^ 3 + B ^ 4 := by ring
  have hB_le : B ≤ (M : ℝ) / 10000000 := by
    have : B ≤ (1 + B) ^ 4 := by
      nlinarith [h1B4, sq_nonneg B, pow_nonneg hB_nonneg 3, pow_nonneg hB_nonneg 4]
    linarith
  have hB2_le : B ^ 2 ≤ (M : ℝ) / 10000000 := by
    have : B ^ 2 ≤ (1 + B) ^ 4 := by
      nlinarith [h1B4, sq_nonneg B, pow_nonneg hB_nonneg 3, pow_nonneg hB_nonneg 4]
    linarith
  have hB4_le : B ^ 4 ≤ (M : ℝ) / 10000000 := by
    have : B ^ 4 ≤ (1 + B) ^ 4 := by
      nlinarith [h1B4, sq_nonneg B, pow_nonneg hB_nonneg 3, pow_nonneg hB_nonneg 4]
    linarith
  let mainTerm (l : List ℕ) : ℝ :=
    (M : ℝ) / (∏ p ∈ l.toFinset, (p : ℝ)) *
      (∏ p ∈ l.toFinset, ∑ r ∈ J, (w r) ^ (l.count p))
  have hlist_mom (l : List ℕ) (hl : ∀ p ∈ l, p ∈ P) :
      |(∑ i ∈ range M, (l.map (fun p => X p i)).prod) - mainTerm l| ≤ A ^ l.length := by
    have hS : ∀ p ∈ l.toFinset, Nat.Prime p ∧ p.Coprime D ∧
        Set.InjOn (fun r : ℕ => r % p) (J : Set ℕ) :=
      fun p hp => hP p (hl p (List.mem_toFinset.mp hp))
    have he : ∀ p ∈ l.toFinset, l.count p ≠ 0 :=
      fun p hp => Nat.ne_of_gt (List.count_pos_iff.mpr (List.mem_toFinset.mp hp))
    have h := distinct_prime_moment (b := b) (M := M) (w := w) hS he
    change |(∑ i ∈ range M, ∏ p ∈ l.toFinset, (X p i) ^ (l.count p)) - mainTerm l| ≤
      A ^ (∑ p ∈ l.toFinset, l.count p) at h
    have hprod_eq : (∑ i ∈ range M, ∏ p ∈ l.toFinset, (X p i) ^ (l.count p)) =
        ∑ i ∈ range M, (l.map (fun p => X p i)).prod :=
      Finset.sum_congr rfl fun i _ => prod_pow_count_toFinset l (fun p => X p i)
    rw [hprod_eq, sum_count_toFinset] at h
    exact h
  have hmain_zero (l : List ℕ) (p : ℕ) (hp : p ∈ l.toFinset) (hc : l.count p = 1) :
      mainTerm l = 0 := by
    dsimp only [mainTerm]
    have hprod0 : (∏ q ∈ l.toFinset, ∑ r ∈ J, (w r) ^ (l.count q)) = 0 :=
      Finset.prod_eq_zero hp (by rw [hc]; simpa using hw0)
    rw [hprod0, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · -- First moment
    have hsum1 : ∑ i ∈ range M, W i = ∑ p ∈ P, ∑ i ∈ range M, X p i := by
      simp_rw [hW_eq]
      exact Finset.sum_comm
    rw [hsum1]
    have hp1 (p : ℕ) (hp : p ∈ P) : |∑ i ∈ range M, X p i| ≤ A := by
      have hm := hlist_mom [p] (by simpa using hp)
      have hmt : mainTerm [p] = 0 := hmain_zero [p] p (by simp) (by simp)
      simpa [hmt] using hm
    calc |∑ p ∈ P, ∑ i ∈ range M, X p i|
      _ ≤ ∑ p ∈ P, |∑ i ∈ range M, X p i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ P, A := Finset.sum_le_sum fun p hp => hp1 p hp
      _ = B := by simp [B]
      _ ≤ (M : ℝ) / 10000000 := hB_le
      _ ≤ (M : ℝ) / 100 := by linarith
  · -- Second moment
    have hsum2 : ∑ i ∈ range M, (W i) ^ 2 =
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ i ∈ range M, X p₁ i * X p₂ i := by
      calc ∑ i ∈ range M, (W i) ^ 2
        _ = ∑ i ∈ range M, (∑ p₁ ∈ P, X p₁ i) * (∑ p₂ ∈ P, X p₂ i) := by
            refine Finset.sum_congr rfl fun i _ => by rw [hW_eq i, sq]
        _ = ∑ i ∈ range M, ∑ p₁ ∈ P, ∑ p₂ ∈ P, X p₁ i * X p₂ i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
        _ = ∑ p₁ ∈ P, ∑ i ∈ range M, ∑ p₂ ∈ P, X p₁ i * X p₂ i := Finset.sum_comm
        _ = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ i ∈ range M, X p₁ i * X p₂ i :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    let m2 (p₁ p₂ : ℕ) : ℝ := if p₁ = p₂ then (M : ℝ) / (p₁ : ℝ) * (∑ r ∈ J, (w r) ^ 2) else 0
    have hm2_eq (p₁ p₂ : ℕ) : mainTerm [p₁, p₂] = m2 p₁ p₂ := by
      by_cases h : p₁ = p₂
      · subst h
        have hset : ([p₁, p₁] : List ℕ).toFinset = {p₁} := by ext x; simp
        have hcnt : ([p₁, p₁] : List ℕ).count p₁ = 2 := by simp
        dsimp only [mainTerm, m2]
        rw [if_pos rfl, hset, Finset.prod_singleton, Finset.prod_singleton, hcnt]
      · dsimp only [m2]
        rw [if_neg h]
        exact hmain_zero [p₁, p₂] p₁ (by simp) (by simp [h])
    have herr2 :
        |(∑ i ∈ range M, (W i) ^ 2) - ∑ p₁ ∈ P, ∑ p₂ ∈ P, m2 p₁ p₂| ≤ B ^ 2 := by
      rw [hsum2, ← Finset.sum_sub_distrib]
      calc |∑ p₁ ∈ P, ((∑ p₂ ∈ P, ∑ i ∈ range M, X p₁ i * X p₂ i) - ∑ p₂ ∈ P, m2 p₁ p₂)|
        _ ≤ ∑ p₁ ∈ P, |(∑ p₂ ∈ P, ∑ i ∈ range M, X p₁ i * X p₂ i) - ∑ p₂ ∈ P, m2 p₁ p₂| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p₁ ∈ P, ∑ p₂ ∈ P, |(∑ i ∈ range M, X p₁ i * X p₂ i) - m2 p₁ p₂| := by
            refine Finset.sum_le_sum fun p₁ _ => ?_
            rw [← Finset.sum_sub_distrib]
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _p₁ ∈ P, ∑ _p₂ ∈ P, A ^ 2 := by
            refine Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ => ?_
            have hl : ∀ q ∈ [p₁, p₂], q ∈ P := by
              intro q hq
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
              rcases hq with rfl | rfl <;> assumption
            have hm := hlist_mom [p₁, p₂] hl
            rw [hm2_eq] at hm
            simpa [mul_one] using hm
        _ = B ^ 2 := by simp [B]; ring
    have hmain2_sum : ∑ p₁ ∈ P, ∑ p₂ ∈ P, m2 p₁ p₂ =
        (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) := by
      calc ∑ p₁ ∈ P, ∑ p₂ ∈ P, m2 p₁ p₂
        _ = ∑ p₁ ∈ P, (M : ℝ) / (p₁ : ℝ) * (∑ r ∈ J, (w r) ^ 2) := by
            refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
            dsimp only [m2]
            rw [Finset.sum_ite_eq, if_pos hp₁]
        _ = ∑ p₁ ∈ P, (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (1 / (p₁ : ℝ))) := by
            refine Finset.sum_congr rfl fun p₁ _ => by ring
        _ = (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hmain2_lb : (M : ℝ) / 1000 ≤ ∑ p₁ ∈ P, ∑ p₂ ∈ P, m2 p₁ p₂ := by
      rw [hmain2_sum]
      have := mul_le_mul_of_nonneg_left hlo hM_nonneg
      linarith
    have herr2' := (abs_le.mp herr2).1
    linarith
  · -- Fourth moment
    have hsum4 : ∑ i ∈ range M, (W i) ^ 4 =
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
          ∑ i ∈ range M, X p₁ i * X p₂ i * X p₃ i * X p₄ i := by
      calc ∑ i ∈ range M, (W i) ^ 4
        _ = ∑ i ∈ range M,
              (∑ p₁ ∈ P, X p₁ i) * (∑ p₂ ∈ P, X p₂ i) *
              (∑ p₃ ∈ P, X p₃ i) * (∑ p₄ ∈ P, X p₄ i) := by
            refine Finset.sum_congr rfl fun i _ => by rw [hW_eq i]; ring
        _ = ∑ i ∈ range M, ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
              X p₁ i * X p₂ i * X p₃ i * X p₄ i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
              ∑ i ∈ range M, X p₁ i * X p₂ i * X p₃ i * X p₄ i := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    have h4_bound :
        ∑ i ∈ range M, (W i) ^ 4 ≤
          (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, mainTerm [p₁, p₂, p₃, p₄]) + B ^ 4 := by
      rw [hsum4]
      have hterm4 : ∀ p₁ ∈ P, ∀ p₂ ∈ P, ∀ p₃ ∈ P, ∀ p₄ ∈ P,
          (∑ i ∈ range M, X p₁ i * X p₂ i * X p₃ i * X p₄ i) ≤
            mainTerm [p₁, p₂, p₃, p₄] + A ^ 4 := by
        intro p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
        have hl : ∀ q ∈ [p₁, p₂, p₃, p₄], q ∈ P := by
          intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with rfl | rfl | rfl | rfl <;> assumption
        have hm := hlist_mom [p₁, p₂, p₃, p₄] hl
        have hprod4 : (∑ i ∈ range M, ([p₁, p₂, p₃, p₄].map (fun p => X p i)).prod) =
            ∑ i ∈ range M, X p₁ i * X p₂ i * X p₃ i * X p₄ i := by
          refine Finset.sum_congr rfl fun i _ => by simp [mul_assoc]
        rw [hprod4] at hm
        have hle := (abs_le.mp hm).2
        have hlen : ([p₁, p₂, p₃, p₄] : List ℕ).length = 4 := rfl
        rw [hlen] at hle
        linarith
      calc ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
              ∑ i ∈ range M, X p₁ i * X p₂ i * X p₃ i * X p₄ i
        _ ≤ ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
              (mainTerm [p₁, p₂, p₃, p₄] + A ^ 4) :=
            Finset.sum_le_sum fun p₁ hp₁ => Finset.sum_le_sum fun p₂ hp₂ =>
              Finset.sum_le_sum fun p₃ hp₃ => Finset.sum_le_sum fun p₄ hp₄ =>
                hterm4 p₁ hp₁ p₂ hp₂ p₃ hp₃ p₄ hp₄
        _ = (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, mainTerm [p₁, p₂, p₃, p₄]) +
              ∑ _p₁ ∈ P, ∑ _p₂ ∈ P, ∑ _p₃ ∈ P, ∑ _p₄ ∈ P, A ^ 4 := by
            simp only [Finset.sum_add_distrib]
        _ = (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, mainTerm [p₁, p₂, p₃, p₄]) + B ^ 4 := by
            congr 1
            simp [B]; ring
    let T0 (p₁ p₂ p₃ p₄ : ℕ) : ℝ :=
      if p₁ = p₂ ∧ p₂ = p₃ ∧ p₃ = p₄ then (M : ℝ) / (p₁ : ℝ) * (∑ r ∈ J, (w r) ^ 4) else 0
    let T1 (p₁ p₂ p₃ p₄ : ℕ) : ℝ :=
      if p₁ = p₂ ∧ p₃ = p₄ then (M : ℝ) / ((p₁ : ℝ) * (p₃ : ℝ)) * (∑ r ∈ J, (w r) ^ 2) ^ 2 else 0
    let T2 (p₁ p₂ p₃ p₄ : ℕ) : ℝ :=
      if p₁ = p₃ ∧ p₂ = p₄ then (M : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ)) * (∑ r ∈ J, (w r) ^ 2) ^ 2 else 0
    let T3 (p₁ p₂ p₃ p₄ : ℕ) : ℝ :=
      if p₁ = p₄ ∧ p₂ = p₃ then (M : ℝ) / ((p₁ : ℝ) * (p₂ : ℝ)) * (∑ r ∈ J, (w r) ^ 2) ^ 2 else 0
    have hT0_nn (p₁ p₂ p₃ p₄ : ℕ) : 0 ≤ T0 p₁ p₂ p₃ p₄ := by
      dsimp only [T0]
      split_ifs
      · exact mul_nonneg (div_nonneg hM_nonneg (Nat.cast_nonneg _))
          (Finset.sum_nonneg fun r _ => by positivity)
      · exact le_rfl
    have hT1_nn (p₁ p₂ p₃ p₄ : ℕ) : 0 ≤ T1 p₁ p₂ p₃ p₄ := by
      dsimp only [T1]
      split_ifs
      · exact mul_nonneg (div_nonneg hM_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          (sq_nonneg _)
      · exact le_rfl
    have hT2_nn (p₁ p₂ p₃ p₄ : ℕ) : 0 ≤ T2 p₁ p₂ p₃ p₄ := by
      dsimp only [T2]
      split_ifs
      · exact mul_nonneg (div_nonneg hM_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          (sq_nonneg _)
      · exact le_rfl
    have hT3_nn (p₁ p₂ p₃ p₄ : ℕ) : 0 ≤ T3 p₁ p₂ p₃ p₄ := by
      dsimp only [T3]
      split_ifs
      · exact mul_nonneg (div_nonneg hM_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
          (sq_nonneg _)
      · exact le_rfl
    have hmain_pair (l : List ℕ) (a b : ℕ) (hab : a ≠ b)
        (hset : l.toFinset = {a, b}) (hca : l.count a = 2) (hcb : l.count b = 2) :
        mainTerm l = (M : ℝ) / ((a : ℝ) * (b : ℝ)) * (∑ r ∈ J, (w r) ^ 2) ^ 2 := by
      dsimp only [mainTerm]
      rw [hset, Finset.prod_pair hab, Finset.prod_pair hab, hca, hcb, sq]
    have hmain4_le (p₁ p₂ p₃ p₄ : ℕ) :
        mainTerm [p₁, p₂, p₃, p₄] ≤
          T0 p₁ p₂ p₃ p₄ + T1 p₁ p₂ p₃ p₄ + T2 p₁ p₂ p₃ p₄ + T3 p₁ p₂ p₃ p₄ := by
      have hn0 := hT0_nn p₁ p₂ p₃ p₄
      have hn1 := hT1_nn p₁ p₂ p₃ p₄
      have hn2 := hT2_nn p₁ p₂ p₃ p₄
      have hn3 := hT3_nn p₁ p₂ p₃ p₄
      by_cases h12 : p₁ = p₂
      · subst h12
        by_cases h34 : p₃ = p₄
        · subst h34
          by_cases h13 : p₁ = p₃
          · subst h13
            have hmt : mainTerm [p₁, p₁, p₁, p₁] = T0 p₁ p₁ p₁ p₁ := by
              have hset : ([p₁, p₁, p₁, p₁] : List ℕ).toFinset = {p₁} := by ext x; simp
              have hcnt : ([p₁, p₁, p₁, p₁] : List ℕ).count p₁ = 4 := by simp
              dsimp only [mainTerm, T0]
              rw [if_pos ⟨rfl, rfl, rfl⟩, hset, Finset.prod_singleton, Finset.prod_singleton, hcnt]
            linarith
          · have hmt : mainTerm [p₁, p₁, p₃, p₃] = T1 p₁ p₁ p₃ p₃ := by
              rw [hmain_pair [p₁, p₁, p₃, p₃] p₁ p₃ h13 (by ext x; simp)
                (by simp [Ne.symm h13]) (by simp [h13])]
              dsimp only [T1]; rw [if_pos ⟨rfl, rfl⟩]
            linarith
        · by_cases h13 : p₁ = p₃
          · subst h13
            have hmt : mainTerm [p₁, p₁, p₁, p₄] = 0 :=
              hmain_zero [p₁, p₁, p₁, p₄] p₄ (by simp) (by simp [h34, Ne.symm h34])
            linarith
          · have hmt : mainTerm [p₁, p₁, p₃, p₄] = 0 :=
              hmain_zero [p₁, p₁, p₃, p₄] p₃ (by simp) (by simp [h13, h34])
            linarith
      · by_cases h13 : p₁ = p₃
        · subst h13
          by_cases h24 : p₂ = p₄
          · subst h24
            have hmt : mainTerm [p₁, p₂, p₁, p₂] = T2 p₁ p₂ p₁ p₂ := by
              rw [hmain_pair [p₁, p₂, p₁, p₂] p₁ p₂ h12 (by ext x; simp)
                (by simp [Ne.symm h12]) (by simp [h12])]
              dsimp only [T2]; rw [if_pos ⟨rfl, rfl⟩]
            linarith
          · have hmt : mainTerm [p₁, p₂, p₁, p₄] = 0 :=
              hmain_zero [p₁, p₂, p₁, p₄] p₂ (by simp) (by simp [h12, Ne.symm h24])
            linarith
        · by_cases h14 : p₁ = p₄
          · subst h14
            by_cases h23 : p₂ = p₃
            · subst h23
              have hmt : mainTerm [p₁, p₂, p₂, p₁] = T3 p₁ p₂ p₂ p₁ := by
                rw [hmain_pair [p₁, p₂, p₂, p₁] p₁ p₂ h12 (by ext x; simp; tauto)
                  (by simp [Ne.symm h12]) (by simp [h12])]
                dsimp only [T3]; rw [if_pos ⟨rfl, rfl⟩]
              linarith
            · have hmt : mainTerm [p₁, p₂, p₃, p₁] = 0 :=
                hmain_zero [p₁, p₂, p₃, p₁] p₂ (by simp) (by simp [h12, Ne.symm h23])
              linarith
          · have hmt : mainTerm [p₁, p₂, p₃, p₄] = 0 :=
              hmain_zero [p₁, p₂, p₃, p₄] p₁ (by simp)
                (by simp [Ne.symm h12, Ne.symm h13, Ne.symm h14])
            linarith
    have hsumT0 :
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T0 p₁ p₂ p₃ p₄ =
          (M : ℝ) * ((∑ r ∈ J, (w r) ^ 4) * (∑ p ∈ P, 1 / (p : ℝ))) := by
      have hcollapse :
          ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T0 p₁ p₂ p₃ p₄ =
            ∑ p₁ ∈ P, (M : ℝ) / (p₁ : ℝ) * (∑ r ∈ J, (w r) ^ 4) := by
        refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
        rw [Finset.sum_eq_single p₁]
        · rw [Finset.sum_eq_single p₁]
          · rw [Finset.sum_eq_single p₁]
            · dsimp only [T0]; rw [if_pos ⟨rfl, rfl, rfl⟩]
            · intro p₄ _ hne; dsimp only [T0]; rw [if_neg (by tauto)]
            · intro hnot; exact absurd hp₁ hnot
          · intro p₃ _ hne
            refine Finset.sum_eq_zero fun p₄ _ => ?_
            dsimp only [T0]; rw [if_neg (by tauto)]
          · intro hnot; exact absurd hp₁ hnot
        · intro p₂ _ hne
          refine Finset.sum_eq_zero fun p₃ _ => Finset.sum_eq_zero fun p₄ _ => ?_
          dsimp only [T0]; rw [if_neg (by tauto)]
        · intro hnot; exact absurd hp₁ hnot
      rw [hcollapse]
      calc ∑ p₁ ∈ P, (M : ℝ) / (p₁ : ℝ) * (∑ r ∈ J, (w r) ^ 4)
        _ = ∑ p₁ ∈ P, (M : ℝ) * ((∑ r ∈ J, (w r) ^ 4) * (1 / (p₁ : ℝ))) :=
            Finset.sum_congr rfl fun _ _ => by ring
        _ = (M : ℝ) * ((∑ r ∈ J, (w r) ^ 4) * (∑ p ∈ P, 1 / (p : ℝ))) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum]
    have hpair_sum :
        ∑ a ∈ P, ∑ c ∈ P, (M : ℝ) / ((a : ℝ) * (c : ℝ)) * (∑ r ∈ J, (w r) ^ 2) ^ 2 =
          (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2 := by
      calc ∑ a ∈ P, ∑ c ∈ P, (M : ℝ) / ((a : ℝ) * (c : ℝ)) * (∑ r ∈ J, (w r) ^ 2) ^ 2
        _ = ∑ a ∈ P, ∑ c ∈ P,
              (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) ^ 2 * ((1 / (a : ℝ)) * (1 / (c : ℝ)))) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) ^ 2 *
              ∑ a ∈ P, ∑ c ∈ P, (1 / (a : ℝ)) * (1 / (c : ℝ))) := by
            simp_rw [← Finset.mul_sum]
        _ = (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2 := by
            have hsq : ∑ a ∈ P, ∑ c ∈ P, (1 / (a : ℝ)) * (1 / (c : ℝ)) =
                (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 := by
              rw [sq, Finset.sum_mul]
              refine Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
            rw [hsq]; ring
    have hsumT1 :
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T1 p₁ p₂ p₃ p₄ =
          (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2 := by
      rw [← hpair_sum]
      refine Finset.sum_congr rfl fun p₁ hp₁ => ?_
      rw [Finset.sum_eq_single p₁]
      · refine Finset.sum_congr rfl fun p₃ hp₃ => ?_
        rw [Finset.sum_eq_single p₃]
        · dsimp only [T1]; rw [if_pos ⟨rfl, rfl⟩]
        · intro p₄ _ hne; dsimp only [T1]; rw [if_neg (by tauto)]
        · intro hnot; exact absurd hp₃ hnot
      · intro p₂ _ hne
        refine Finset.sum_eq_zero fun p₃ _ => Finset.sum_eq_zero fun p₄ _ => ?_
        dsimp only [T1]; rw [if_neg (by tauto)]
      · intro hnot; exact absurd hp₁ hnot
    have hsumT2 :
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T2 p₁ p₂ p₃ p₄ =
          (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2 := by
      rw [← hpair_sum]
      refine Finset.sum_congr rfl fun p₁ hp₁ => Finset.sum_congr rfl fun p₂ hp₂ => ?_
      rw [Finset.sum_eq_single p₁]
      · rw [Finset.sum_eq_single p₂]
        · dsimp only [T2]; rw [if_pos ⟨rfl, rfl⟩]
        · intro p₄ _ hne; dsimp only [T2]; rw [if_neg (by tauto)]
        · intro hnot; exact absurd hp₂ hnot
      · intro p₃ _ hne
        refine Finset.sum_eq_zero fun p₄ _ => ?_
        dsimp only [T2]; rw [if_neg (by tauto)]
      · intro hnot; exact absurd hp₁ hnot
    have hsumT3 :
        ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T3 p₁ p₂ p₃ p₄ =
          (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2 := by
      rw [← hpair_sum]
      refine Finset.sum_congr rfl fun p₁ hp₁ => Finset.sum_congr rfl fun p₂ hp₂ => ?_
      rw [Finset.sum_eq_single p₂]
      · rw [Finset.sum_eq_single p₁]
        · dsimp only [T3]; rw [if_pos ⟨rfl, rfl⟩]
        · intro p₄ _ hne; dsimp only [T3]; rw [if_neg (by tauto)]
        · intro hnot; exact absurd hp₁ hnot
      · intro p₃ _ hne
        refine Finset.sum_eq_zero fun p₄ _ => ?_
        dsimp only [T3]; rw [if_neg (by tauto)]
      · intro hnot; exact absurd hp₂ hnot
    have hmain4_sum_le :
        (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, mainTerm [p₁, p₂, p₃, p₄]) ≤
          (M : ℝ) * ((∑ r ∈ J, (w r) ^ 4) * (∑ p ∈ P, 1 / (p : ℝ))) +
          3 * ((M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2) := by
      calc ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, mainTerm [p₁, p₂, p₃, p₄]
        _ ≤ ∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
              (T0 p₁ p₂ p₃ p₄ + T1 p₁ p₂ p₃ p₄ + T2 p₁ p₂ p₃ p₄ + T3 p₁ p₂ p₃ p₄) :=
            Finset.sum_le_sum fun p₁ _ => Finset.sum_le_sum fun p₂ _ =>
              Finset.sum_le_sum fun p₃ _ => Finset.sum_le_sum fun p₄ _ =>
                hmain4_le p₁ p₂ p₃ p₄
        _ = (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T0 p₁ p₂ p₃ p₄) +
            (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T1 p₁ p₂ p₃ p₄) +
            (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T2 p₁ p₂ p₃ p₄) +
            (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P, T3 p₁ p₂ p₃ p₄) := by
            simp only [Finset.sum_add_distrib]
        _ = (M : ℝ) * ((∑ r ∈ J, (w r) ^ 4) * (∑ p ∈ P, 1 / (p : ℝ))) +
            3 * ((M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2) := by
            rw [hsumT0, hsumT1, hsumT2, hsumT3]; ring
    have h4_term1 :
        (M : ℝ) * ((∑ r ∈ J, (w r) ^ 4) * (∑ p ∈ P, 1 / (p : ℝ))) ≤ (M : ℝ) * (1 / 1000000) :=
      mul_le_mul_of_nonneg_left h4 hM_nonneg
    have hhi_sq :
        ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2 ≤ (11 / 10000 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg fun r _ => sq_nonneg _)
        (Finset.sum_nonneg fun p _ => by positivity)) hhi 2
    have h4_term2 :
        (M : ℝ) * ((∑ r ∈ J, (w r) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))) ^ 2 ≤
          (M : ℝ) * (11 / 10000 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hhi_sq hM_nonneg
    linarith
