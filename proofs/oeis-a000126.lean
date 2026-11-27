import OMAStatements.S_oeis_a000126

-- Problem: A000126, Layman's conjecture |S(n)| = F(n+3) - (n+1) for the sets S(1) = {1},
-- S(n+1) = {x+1 : x ∈ S(n)} ∪ {2x+1 : x ∈ S(n)}.
-- Credit: @ShoQo
-- Proof: formalizes Sela Fried's argument (https://oeis.org/A000126/a000126.pdf): min S(n) = n,
-- {n..2n-1} ⊆ S(n), non-minimal elements persist, a halving lemma, and the bijection
-- x ↦ 2x+3 from S(n) \ {n} onto the overlap at level n+3, giving s(n) = 2s(n-1) - s(n-3) + 1.

open OMA.S_oeis_a000126

namespace OMA_A000126_Proof

lemma mem_succ {n x : ℕ} (hn : 1 ≤ n) :
    x ∈ laymanSet (n + 1) ↔ ∃ y ∈ laymanSet n, x = y + 1 ∨ x = 2 * y + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [laymanSet, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, hy, Or.inl rfl⟩
    · exact ⟨y, hy, Or.inr rfl⟩
  · rintro ⟨y, hy, rfl | rfl⟩
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩

lemma add_one_mem {n y : ℕ} (hn : 1 ≤ n) (hy : y ∈ laymanSet n) : y + 1 ∈ laymanSet (n + 1) :=
  (mem_succ hn).mpr ⟨y, hy, Or.inl rfl⟩

lemma two_mul_add_one_mem {n y : ℕ} (hn : 1 ≤ n) (hy : y ∈ laymanSet n) : 2 * y + 1 ∈ laymanSet (n + 1) :=
  (mem_succ hn).mpr ⟨y, hy, Or.inr rfl⟩

/-- Lemma 1 (Fried): every element of `laymanSet n` is at least `n`, and `n ∈ laymanSet n`. -/
lemma le_of_mem : ∀ {n x : ℕ}, 1 ≤ n → x ∈ laymanSet n → n ≤ x := by
  intro n
  induction n with
  | zero => intro x h; omega
  | succ k ih =>
    intro x _ hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [laymanSet] at hx; omega
    · obtain ⟨y, hy, rfl | rfl⟩ := (mem_succ hk).mp hx
      · have := ih hk hy; omega
      · have := ih hk hy; omega

lemma self_mem : ∀ n : ℕ, 1 ≤ n → n ∈ laymanSet n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp [laymanSet]
  | succ k hk ih => exact add_one_mem hk ih

/-- Lemma 2: `{n, ..., 2n - 1} ⊆ laymanSet n`. -/
lemma Icc_mem : ∀ n : ℕ, 1 ≤ n → ∀ x, n ≤ x → x ≤ 2 * n - 1 → x ∈ laymanSet n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro x h1 h2; simp [laymanSet]; omega
  | succ k hk ih =>
    intro x h1 h2
    rcases Nat.lt_or_ge x (2 * k + 1) with h | h
    · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
      exact add_one_mem hk (ih y (by omega) (by omega))
    · rw [show x = 2 * k + 1 by omega]
      exact two_mul_add_one_mem hk (self_mem k hk)

/-- Lemma 3: non-minimal elements persist. -/
lemma mem_succ_of_ne : ∀ n : ℕ, 1 ≤ n → ∀ x, x ∈ laymanSet n → x ≠ n → x ∈ laymanSet (n + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro x hx hne; simp [laymanSet] at hx; omega
  | succ k hk ih =>
    intro x hx hne
    have hgt : k + 1 < x := lt_of_le_of_ne (le_of_mem (by omega) hx) (Ne.symm hne)
    obtain ⟨y, hy, rfl | rfl⟩ := (mem_succ hk).mp hx
    · exact add_one_mem (by omega) (ih y hy (by omega))
    · by_cases hyk : y = k
      · subst hyk
        rw [show 2 * y + 1 = (2 * y) + 1 from rfl]
        exact add_one_mem (by omega) (Icc_mem (y + 1) (by omega) (2 * y) (by omega) (by omega))
      · exact two_mul_add_one_mem (by omega) (ih y hy hyk)

/-- Corollary 1. -/
lemma succ_mem_add_two {n x : ℕ} (hn : 1 ≤ n) (hx : x ∈ laymanSet n) (hne : x ≠ n) : x + 1 ∈ laymanSet (n + 2) :=
  add_one_mem (by omega) (mem_succ_of_ne n hn x hx hne)

/-- Lemma 4: halving. -/
lemma mem_of_two_mul_add_one : ∀ n : ℕ, 1 ≤ n → ∀ x, n < x → 2 * x + 1 ∈ laymanSet (n + 1) → x ∈ laymanSet n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn x hxn hx
    obtain ⟨y, hy, h | h⟩ := (mem_succ hn).mp hx
    · -- 2x = y ∈ laymanSet n
      have hy' : 2 * x ∈ laymanSet n := by rw [show 2 * x = y by omega]; exact hy
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have : n = 1 := by omega
        subst this; simp [laymanSet] at hy'
      obtain ⟨z, hz, hz1 | hz1⟩ := (mem_succ (n := n - 1) (by omega)).mp
        (by rw [show n - 1 + 1 = n by omega]; exact hy')
      · -- z = 2(x-1)+1 ∈ laymanSet (n-1)
        rcases Nat.lt_or_ge n 3 with h3 | h3
        · have : n = 2 := by omega
          subst this; simp [laymanSet] at hz; omega
        have hz' : 2 * (x - 1) + 1 ∈ laymanSet (n - 2 + 1) := by
          rw [show n - 2 + 1 = n - 1 by omega, show 2 * (x - 1) + 1 = z by omega]; exact hz
        have hx1 : x - 1 ∈ laymanSet (n - 2) := ih (n - 2) (by omega) (by omega) (x - 1) (by omega) hz'
        have hx2 : x ∈ laymanSet (n - 1) := by
          have := add_one_mem (n := n - 2) (by omega) hx1
          rwa [show x - 1 + 1 = x by omega, show n - 2 + 1 = n - 1 by omega] at this
        have := mem_succ_of_ne (n - 1) (by omega) x hx2 (by omega)
        rwa [show n - 1 + 1 = n by omega] at this
      · omega
    · rw [show x = y by omega]; exact hy

/-- The overlap `A ∩ B` at level `m + 3` is the image of `laymanSet m \ {m}` under `x ↦ 2x + 3`. -/
lemma inter_eq (m : ℕ) (hm : 1 ≤ m) :
    (laymanSet (m + 2)).image (fun x => x + 1) ∩ (laymanSet (m + 2)).image (fun x => 2 * x + 1)
      = ((laymanSet m).erase m).image (fun x => 2 * x + 3) := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, hv'⟩⟩
    have hvge : m + 2 ≤ v := le_of_mem (by omega) hv
    -- u = 2v ∈ laymanSet (m + 2) comes from 2(v-1)+1 ∈ laymanSet (m + 1)
    obtain ⟨c, hc, hc1 | hc1⟩ := (mem_succ (n := m + 1) (by omega)).mp hu
    · have hc' : 2 * (v - 1) + 1 ∈ laymanSet (m + 1) := by rw [show 2 * (v - 1) + 1 = c by omega]; exact hc
      refine ⟨v - 1, ⟨by omega, mem_of_two_mul_add_one m hm (v - 1) (by omega) hc'⟩, by omega⟩
    · omega
  · rintro ⟨x, ⟨hne, hx⟩, rfl⟩
    refine ⟨⟨2 * x + 2, ?_, by ring⟩, ⟨x + 1, succ_mem_add_two hm hx hne, by ring⟩⟩
    have h1 := two_mul_add_one_mem hm hx
    exact add_one_mem (by omega) h1

lemma card_rec (m : ℕ) (hm : 1 ≤ m) :
    ((laymanSet (m + 3)).card : ℤ) = 2 * (laymanSet (m + 2)).card - (laymanSet m).card + 1 := by
  have hA : ((laymanSet (m + 2)).image (fun x => x + 1)).card = (laymanSet (m + 2)).card :=
    Finset.card_image_of_injective _ (fun a b h => by simpa using h)
  have hB : ((laymanSet (m + 2)).image (fun x => 2 * x + 1)).card = (laymanSet (m + 2)).card :=
    Finset.card_image_of_injective _ (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega)
  have hI : (((laymanSet m).erase m).image (fun x => 2 * x + 3)).card = (laymanSet m).card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b (h : 2 * a + 3 = 2 * b + 3) => by omega),
      Finset.card_erase_of_mem (self_mem m hm)]
  have hpos : 1 ≤ (laymanSet m).card := Finset.card_pos.mpr ⟨m, self_mem m hm⟩
  have hu := Finset.card_union_add_card_inter ((laymanSet (m + 2)).image (fun x => x + 1))
    ((laymanSet (m + 2)).image (fun x => 2 * x + 1))
  rw [inter_eq m hm, hA, hB, hI] at hu
  have hS : laymanSet (m + 3) = (laymanSet (m + 2)).image (fun x => x + 1) ∪ (laymanSet (m + 2)).image (fun x => 2 * x + 1) := rfl
  rw [hS]
  omega

end OMA_A000126_Proof

open OMA_A000126_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a000126.main := by
  have key : ∀ n : ℕ, 1 ≤ n → ((laymanSet n).card : ℤ) = Nat.fib (n + 3) - n - 1 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n, hn, ih with
      | 1, _, _ => decide
      | 2, _, _ => decide
      | 3, _, _ => decide
      | (m + 4), _, ih =>
        rw [show m + 4 = (m + 1) + 3 by ring, card_rec (m + 1) (by omega),
          ih (m + 1 + 2) (by omega) (by omega), ih (m + 1) (by omega) (by omega)]
        rw [show m + 1 + 3 + 3 = (m + 5) + 2 by ring, Nat.fib_add_two (n := m + 5),
          show m + 1 + 2 + 3 = m + 6 by ring, show m + 5 + 1 = m + 6 by ring,
          show m + 1 + 3 = m + 4 by ring, Nat.fib_add_two (n := m + 4)]
        push_cast; ring
  intro n hn
  have := key n hn
  unfold a
  omega

