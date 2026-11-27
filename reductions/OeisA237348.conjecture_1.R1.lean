import FormalConjectures.OEIS.«237348»

/-!
# Removing higher prime powers from Sun's prime-index representations

On a block starting at 16^t, a higher prime power below or equal to 64^t has
base at most 8^t and exponent at most 6t. Each value removes at most one
index on each side of the sum. Credit: @Pixelstorm44.
-/
namespace OMA.R_OeisA237348_conjecture_1_R1

-- A lower bound for the prime-power correlation on each geometric block.
def H1 : Prop := ∀ d : ℕ, 1 ≤ d → ∃ T : ℕ, ∀ t ≥ T, ∀ n : ℕ,
    16 ^ t ≤ n → n < 16 ^ (t + 1) →
    let p := fun j : ℕ => Nat.nth Nat.Prime (j - 1)
    2 * ((8 ^ t + 1) * (6 * t + 1)) <
      ((Finset.Ico 1 n).filter fun k =>
        IsPrimePow (p k + 2*d) ∧ IsPrimePow (p (p (n-k)) + 2*d)).card

-- A coarse growth estimate for the prime with prime index at a block endpoint.
def H2 : Prop := ∀ d : ℕ, 1 ≤ d → ∃ T : ℕ, ∀ t ≥ T,
    let p := fun j : ℕ => Nat.nth Nat.Prime (j - 1)
    p (p (16 ^ (t + 1))) + 2*d ≤ 64 ^ t

-- An injective sequence with values up to 64^t has few nonprime prime powers.
theorem count_higher_powers (t : ℕ) (s : Finset ℕ) (f : ℕ → ℕ)
    (hinj : Set.InjOn f (s : Set ℕ))
    (hs : ∀ k ∈ s, IsPrimePow (f k) ∧ ¬ (f k).Prime ∧ f k ≤ 64 ^ t) :
    s.card ≤ (8 ^ t + 1) * (6*t + 1) := by
  classical
  let box := (Finset.range (8 ^ t + 1)).product (Finset.range (6*t + 1))
  let values := box.image fun z : ℕ × ℕ => z.1 ^ z.2
  have maps : Set.MapsTo f (s : Set ℕ) (values : Set ℕ) := by
    intro k hk
    obtain ⟨hpow, hcomp, hbound⟩ := hs k hk
    obtain ⟨p, e, hp, he, hval⟩ := (isPrimePow_nat_iff _).mp hpow
    have he2 : 2 ≤ e := by
      by_contra! h
      have : e = 1 := by omega
      simp [this] at hval
      exact hcomp (hval ▸ hp)
    have hsq : p^2 ≤ (8^t)^2 := calc
      p^2 ≤ p^e := Nat.pow_le_pow_right hp.pos he2
      _ = f k := hval
      _ ≤ 64^t := hbound
      _ = (8^t)^2 := by rw [← Nat.pow_right_comm]
    have hbase : p ≤ 8 ^ t := (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp hsq
    have hexp : 2^e ≤ 2^(6*t) := calc
      2^e ≤ p^e := Nat.pow_le_pow_left hp.two_le e
      _ = f k := hval
      _ ≤ 64^t := hbound
      _ = 2^(6*t) := by rw [pow_mul]; rfl
    have hemax : e ≤ 6*t := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hexp
    exact Finset.mem_image.mpr ⟨(p,e), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, hval⟩
  calc
    s.card ≤ values.card := Finset.card_le_card_of_injOn f maps hinj
    _ ≤ box.card := Finset.card_image_le
    _ = _ := by simp [box]

theorem main : H1 → H2 → type_of% @OeisA237348.conjecture_1 := by
  classical
  intro corr growth d hd
  obtain ⟨T, hc⟩ := corr d hd
  obtain ⟨U, hu⟩ := growth d hd
  refine ⟨16^(max T U), by positivity, ?_⟩
  intro n hn
  let t := Nat.log 16 n
  have ht : max T U ≤ t := Nat.le_log_of_pow_le (by decide) hn.le
  have hlo := Nat.pow_log_le_self 16 (Nat.ne_zero_of_lt hn)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 16) n
  let p := fun j : ℕ => Nat.nth Nat.Prime (j - 1)
  have hmono : Monotone p := fun _ _ h =>
    (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone (by omega)
  have pinj {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : p a = p b) : a = b := by
    have := (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective h
    omega
  have ppos (a : ℕ) : 0 < p a := (Nat.prime_nth_prime _).pos
  let f := fun k : ℕ => p k + 2*d
  let g := fun k : ℕ => p (p (n-k)) + 2*d
  let s := (Finset.Ico 1 n).filter fun k => IsPrimePow (f k) ∧ IsPrimePow (g k)
  have hlarge : 2 * ((8 ^ t + 1) * (6*t + 1)) < s.card :=
    hc t ((le_max_left ..).trans ht) n hlo hhi
  have hbound : p (p (16^(t+1))) + 2*d ≤ 64^t := hu t ((le_max_right ..).trans ht)
  have indices {k : ℕ} (hk : k ∈ s) : 1 ≤ k ∧ k < n :=
    Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1
  let badF := s.filter fun k => ¬ (f k).Prime
  let badG := s.filter fun k => ¬ (g k).Prime
  have hf : badF.card ≤ (8 ^ t + 1) * (6*t + 1) := by
    apply count_higher_powers t badF f
    · intro a ha b hb he
      exact pinj (indices (Finset.mem_filter.mp ha).1).1
        (indices (Finset.mem_filter.mp hb).1).1 (Nat.add_right_cancel he)
    · intro k hk
      obtain ⟨hs, hb⟩ := Finset.mem_filter.mp hk
      have hkn := (indices hs).2
      have hbig := Nat.add_two_le_nth_prime (16^(t+1)-1)
      have hkp : k ≤ p (16^(t+1)) := by dsimp [p]; change n < 16^(t+1) at hhi; omega
      exact ⟨(Finset.mem_filter.mp hs).2.1, hb,
        (Nat.add_le_add_right (hmono hkp) _).trans hbound⟩
  have hg : badG.card ≤ (8 ^ t + 1) * (6*t + 1) := by
    apply count_higher_powers t badG g
    · intro a ha b hb he
      have ha' := (indices (Finset.mem_filter.mp ha).1).2
      have hb' := (indices (Finset.mem_filter.mp hb).1).2
      have hab := pinj (ppos (n-a)) (ppos (n-b)) (Nat.add_right_cancel he)
      have := pinj (by omega : 0 < n-a) (by omega : 0 < n-b) hab
      omega
    · intro k hk
      obtain ⟨hs, hb⟩ := Finset.mem_filter.mp hk
      have hnk : n-k ≤ 16^(t+1) := (Nat.sub_le ..).trans hhi.le
      exact ⟨(Finset.mem_filter.mp hs).2.2, hb,
        (Nat.add_le_add_right (hmono (hmono hnk)) _).trans hbound⟩
  by_contra hnone
  have sub : s ⊆ badF ∪ badG := by
    intro k hk
    by_cases hf' : (f k).Prime
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hk, fun hg' => hnone ?_⟩
      obtain ⟨hkpos, hkn⟩ := indices hk
      exact ⟨k, n-k, hkpos, by omega, by omega, hf', hg'⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hf'⟩)
  have hcard := (Finset.card_le_card sub).trans (Finset.card_union_le badF badG)
  omega

end OMA.R_OeisA237348_conjecture_1_R1
