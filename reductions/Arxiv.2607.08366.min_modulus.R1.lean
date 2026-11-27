import FormalConjectures.Arxiv.«2607.08366».MinModulus

-- Reduction Arxiv.2607.08366.min_modulus.R1 of Conjecture 1 (Fonollosa, 2026).
-- Credit: @rorcores
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Idea: a 2-adic descent.  For an even modulus `N = 2 * M`, split a valid set by the parity of its
-- elements.  If both parity classes have at least two elements we are in the situation of `H2`.
-- Otherwise one class holds all but at most one element; it lies in a coset of the even subgroup,
-- which is a copy of `ZMod M`, and it is still valid there (`halve`).  Induction on the modulus,
-- with `H1` for odd moduli, gives for every valid `n`-set modulo `N` a `v` with
-- `2 ^ v ∣ N` and `2 ^ n ≤ N + 2 ^ v` (`descent`).  Below `2 ^ n` this forces `N = 2 ^ n - 2 ^ v`,
-- and `N < minModulus n` forces `n < 2 ^ v`, which is exactly the case excluded by `H3`.

namespace OMA.R_Arxiv_2607_08366_min_modulus_R1

open Finset Arxiv.«2607.08366»

/-- Odd moduli: a valid `n`-set modulo an odd `N` needs `N ≥ 2 ^ n - 1`. -/
def H1 : Prop :=
  ∀ n N : ℕ, N % 2 = 1 → ∀ A : Finset (ZMod N), #A = n → IsValidMod A → 2 ^ n ≤ N + 1

/-- Balanced even moduli: if `N` is even and a valid `n`-set has at least two elements of each
parity, then `N ≥ 2 ^ n`. -/
def H2 : Prop :=
  ∀ n N : ℕ, 0 < N → N % 2 = 0 → ∀ A : Finset (ZMod N), #A = n → IsValidMod A →
    2 ≤ #(A.filter fun a => a.val % 2 = 0) → 2 ≤ #(A.filter fun a => a.val % 2 = 1) → 2 ^ n ≤ N

/-- The cap: there is no valid `n`-set modulo `2 ^ n - 2 ^ v` when `2 ^ v > n`. -/
def H3 : Prop :=
  ∀ n v : ℕ, v < n → n < 2 ^ v → ∀ A : Finset (ZMod (2 ^ n - 2 ^ v)), #A = n → ¬ IsValidMod A

/-- Validity passes to subsets: a multiplicity vector on `B` is extended by ones on `A \ B`. -/
lemma isValidMod_subset {N : ℕ} {A B : Finset (ZMod N)} (hBA : B ⊆ A) (hA : IsValidMod A) :
    IsValidMod B := by
  classical
  intro m hsize hsum b hb
  have h1 : ∑ a ∈ A, (if a ∈ B then m a else 1) = #A := by
    rw [← Finset.sum_sdiff hBA]
    have e1 : ∑ a ∈ A \ B, (if a ∈ B then m a else 1) = #(A \ B) := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_neg (Finset.mem_sdiff.1 ha).2]
    have e2 : ∑ a ∈ B, (if a ∈ B then m a else 1) = #B := by
      rw [← hsize]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_pos ha]
    rw [e1, e2, Finset.card_sdiff_add_card_eq_card hBA]
  have h2 : ∑ a ∈ A, (((if a ∈ B then m a else 1 : ℕ) : ZMod N)) * a = ∑ a ∈ A, a := by
    rw [← Finset.sum_sdiff hBA, ← Finset.sum_sdiff hBA (f := fun a => a)]
    have e1 : ∑ a ∈ A \ B, (((if a ∈ B then m a else 1 : ℕ) : ZMod N)) * a = ∑ a ∈ A \ B, a := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_neg (Finset.mem_sdiff.1 ha).2, Nat.cast_one, one_mul]
    have e2 : ∑ a ∈ B, (((if a ∈ B then m a else 1 : ℕ) : ZMod N)) * a = ∑ a ∈ B, a := by
      rw [← hsum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_pos ha]
    rw [e1, e2]
  have key := hA (fun a => if a ∈ B then m a else 1) h1 h2 b (hBA hb)
  simpa [hb] using key

/-- A valid set all of whose elements have the same parity modulo `2 * M` gives a valid set of the
same size modulo `M`: translate by the parity and divide by two. -/
lemma halve {M : ℕ} (hM : 0 < M) (C : Finset (ZMod (2 * M))) (p : ℕ)
    (hp : ∀ a ∈ C, a.val % 2 = p) (hC : IsValidMod C) :
    ∃ C' : Finset (ZMod M), #C' = #C ∧ IsValidMod C' := by
  classical
  have : NeZero (2 * M) := ⟨by omega⟩
  have : NeZero M := ⟨by omega⟩
  have hinj : Set.InjOn (fun a : ZMod (2 * M) => ((a.val / 2 : ℕ) : ZMod M)) (C : Set (ZMod (2 * M))) := by
    intro a ha b hb hab
    have ha : a ∈ C := ha
    have hb : b ∈ C := hb
    have hab : ((a.val / 2 : ℕ) : ZMod M) = ((b.val / 2 : ℕ) : ZMod M) := hab
    have ha2 : a.val / 2 < M := by have := ZMod.val_lt a; omega
    have hb2 : b.val / 2 < M := by have := ZMod.val_lt b; omega
    have hq : a.val / 2 = b.val / 2 := by
      have h := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hab
      rwa [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at h
    apply ZMod.val_injective
    have h1 := hp a ha
    have h2 := hp b hb
    omega
  refine ⟨C.image fun a => ((a.val / 2 : ℕ) : ZMod M), Finset.card_image_of_injOn hinj, ?_⟩
  intro m' hsize hsum c' hc'
  obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 hc'
  rw [Finset.sum_image hinj, Finset.card_image_of_injOn hinj] at hsize
  rw [Finset.sum_image hinj, Finset.sum_image hinj] at hsum
  -- the hypothesis on sums, as a congruence between natural numbers modulo `M`
  have hS : (∑ a ∈ C, m' ((a.val / 2 : ℕ) : ZMod M) * (a.val / 2)) ≡ (∑ a ∈ C, a.val / 2) [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    exact hsum
  -- every element of `C` is `2 * (a.val / 2) + p`
  have hval : ∀ a ∈ C, a = ((2 * (a.val / 2) + p : ℕ) : ZMod (2 * M)) := by
    intro a ha
    have h1 := hp a ha
    have h2 : 2 * (a.val / 2) + p = a.val := by omega
    rw [h2, ZMod.natCast_zmod_val]
  have key := hC (fun a => m' ((a.val / 2 : ℕ) : ZMod M)) hsize ?_ a₀ ha₀
  · exact key
  · have hL : ∑ a ∈ C, ((m' ((a.val / 2 : ℕ) : ZMod M) : ℕ) : ZMod (2 * M)) * a
        = ((∑ a ∈ C, m' ((a.val / 2 : ℕ) : ZMod M) * (2 * (a.val / 2) + p) : ℕ) : ZMod (2 * M)) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Nat.cast_mul]
      congr 1
      exact hval a ha
    have hR : ∑ a ∈ C, a = ((∑ a ∈ C, (2 * (a.val / 2) + p) : ℕ) : ZMod (2 * M)) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun a ha => hval a ha
    rw [hL, hR, ZMod.natCast_eq_natCast_iff]
    have e1 : ∑ a ∈ C, m' ((a.val / 2 : ℕ) : ZMod M) * (2 * (a.val / 2) + p)
        = 2 * (∑ a ∈ C, m' ((a.val / 2 : ℕ) : ZMod M) * (a.val / 2)) + p * #C := by
      rw [← hsize, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    have e2 : ∑ a ∈ C, (2 * (a.val / 2) + p) = 2 * (∑ a ∈ C, a.val / 2) + p * #C := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_comm p]
    rw [e1, e2]
    exact (Nat.ModEq.mul_left' 2 hS).add_right _

/-- The 2-adic descent: every valid `n`-set modulo `N` has `2 ^ n ≤ N + 2 ^ v` for some `v` with
`2 ^ v ∣ N`. -/
lemma descent (h1 : H1) (h2 : H2) :
    ∀ N : ℕ, 0 < N → ∀ (n : ℕ) (A : Finset (ZMod N)), #A = n → IsValidMod A →
      ∃ v : ℕ, 2 ^ v ∣ N ∧ 2 ^ n ≤ N + 2 ^ v := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN n A hA hvalid
    rcases Nat.mod_two_eq_zero_or_one N with hpar | hpar
    · -- even modulus
      obtain ⟨M, rfl⟩ : ∃ M, N = 2 * M := ⟨N / 2, by omega⟩
      have hM : 0 < M := by omega
      by_cases hbal : 2 ≤ #(A.filter fun a => a.val % 2 = 0) ∧ 2 ≤ #(A.filter fun a => a.val % 2 = 1)
      · refine ⟨0, one_dvd _, ?_⟩
        have := h2 n (2 * M) hN hpar A hA hvalid hbal.1 hbal.2
        omega
      · -- one parity class contains all but at most one element
        have hsplit : #(A.filter fun a => a.val % 2 = 0) + #(A.filter fun a => a.val % 2 = 1) = n := by
          have h := Finset.card_filter_add_card_filter_not (s := A)
            (fun a : ZMod (2 * M) => a.val % 2 = 0)
          have e : (A.filter fun a => ¬ a.val % 2 = 0) = A.filter fun a => a.val % 2 = 1 :=
            Finset.filter_congr fun a _ => by omega
          rw [e] at h
          omega
        obtain ⟨C, p, hCA, hCp, hCn⟩ : ∃ (C : Finset (ZMod (2 * M))) (p : ℕ),
            C ⊆ A ∧ (∀ a ∈ C, a.val % 2 = p) ∧ n ≤ #C + 1 := by
          rcases Nat.lt_or_ge (#(A.filter fun a => a.val % 2 = 1)) 2 with hO | hO
          · exact ⟨_, 0, Finset.filter_subset _ _, fun a ha => (Finset.mem_filter.1 ha).2, by omega⟩
          · have hE : #(A.filter fun a => a.val % 2 = 0) < 2 := by
              by_contra hcon
              exact hbal ⟨by omega, hO⟩
            exact ⟨_, 1, Finset.filter_subset _ _, fun a ha => (Finset.mem_filter.1 ha).2, by omega⟩
        obtain ⟨C', hC'card, hC'valid⟩ := halve hM C p hCp (isValidMod_subset hCA hvalid)
        obtain ⟨v, hv, hle⟩ := ih M (by omega) hM (#C') C' rfl hC'valid
        refine ⟨v + 1, ?_, ?_⟩
        · rw [pow_succ, mul_comm]
          exact Nat.mul_dvd_mul_left 2 hv
        · have hpow : 2 ^ n ≤ 2 ^ (#C + 1) := Nat.pow_le_pow_right (by norm_num) hCn
          rw [hC'card] at hle
          rw [pow_succ] at hpow ⊢
          omega
    · -- odd modulus
      exact ⟨0, one_dvd _, by simpa using h1 n N hpar A hA hvalid⟩

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2607.08366».min_modulus := by
  intro h1 h2 h3 n N hn hN hlt A hA hvalid
  obtain ⟨v, ⟨k, hk⟩, hle⟩ := descent h1 h2 N hN n A hA hvalid
  have hlt' : N < 2 ^ n - 2 ^ Nat.log 2 n := hlt
  have hlogpos : 0 < 2 ^ Nat.log 2 n := by positivity
  have hnpos : 0 < 2 ^ n := by positivity
  have hNlt : N < 2 ^ n := by omega
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0, mul_zero] at hk
      omega
    · exact h0
  have hvpos : 0 < 2 ^ v := by positivity
  -- `v < n`, since `2 ^ v ≤ N < 2 ^ n`
  have hvn : v < n := by
    by_contra hcon
    have h2v : 2 ^ n ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ v ≤ 2 ^ v * k := Nat.le_mul_of_pos_right _ hkpos
    omega
  have hpow : 2 ^ n = 2 ^ v * 2 ^ (n - v) := by
    rw [← pow_add]
    congr 1
    omega
  -- `k = 2 ^ (n - v) - 1`
  have ha : 2 ^ (n - v) ≤ k + 1 := by
    have : 2 ^ v * 2 ^ (n - v) ≤ 2 ^ v * (k + 1) := by
      rw [← hpow, mul_add, mul_one, ← hk]
      exact hle
    exact Nat.le_of_mul_le_mul_left this hvpos
  have hb : k < 2 ^ (n - v) := by
    have : 2 ^ v * k < 2 ^ v * 2 ^ (n - v) := by
      rw [← hpow, ← hk]
      exact hNlt
    exact Nat.lt_of_mul_lt_mul_left this
  have hNeq : N = 2 ^ n - 2 ^ v := by
    have : 2 ^ v * (k + 1) = 2 ^ n := by
      rw [hpow]
      congr 1
      omega
    rw [mul_add, mul_one, ← hk] at this
    omega
  -- `n < 2 ^ v`, since `2 ^ n - 2 ^ v < 2 ^ n - 2 ^ log₂ n`
  have hlog : Nat.log 2 n < v := by
    have h2 : 2 ^ Nat.log 2 n < 2 ^ v := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 h2
  have hnv : n < 2 ^ v := Nat.lt_pow_of_log_lt (by norm_num) hlog
  subst hNeq
  exact h3 n v hvn hnv A hA hvalid

end OMA.R_Arxiv_2607_08366_min_modulus_R1
