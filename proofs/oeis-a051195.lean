import OMAStatements.S_oeis_a051195

-- OEIS A051195. Credit: @yuka30240. Earlier proof: Left to Solve PR #7037.
-- The number of identical blocks divides both the length and the weight.
-- This forces exactly two blocks, and the first half determines the word.
namespace OMA.S_oeis_a051195

open Finset
open scoped Classical

private def double (l : ℕ) (b : Finset ℕ) := b ∪ b.image (l + ·)

private lemma periodic {n : ℕ} {w : Finset ℕ} : repeated n w ↔
    ∃ b ⊆ range (n + 1), n = 2 * b.card ∧ double (n + 1) b = w := by
  have copies_two (l : ℕ) (b : Finset ℕ) : copies 2 l b = double l b := by
    simp [copies, range_add_one, double, biUnion_insert, union_comm]
  constructor
  · rintro ⟨r, l, b, hr, _, hb, hl, hn, rfl⟩
    have h : r ∣ 2 := by
      have length_dvd : r ∣ 2 * n + 2 := ⟨l, hl⟩
      have weight_dvd : r ∣ 2 * n := dvd_mul_of_dvd_right (show r ∣ n from ⟨_, hn⟩) 2
      simpa using Nat.dvd_sub length_dvd weight_dvd
    have := Nat.le_of_dvd (by decide : 0 < 2) h
    obtain rfl : r = 2 := by omega
    obtain rfl : l = n + 1 := by omega
    exact ⟨b, hb, hn, (copies_two _ _).symm⟩
  · rintro ⟨b, hb, hn, rfl⟩
    exact ⟨2, n + 1, b, by decide, by omega, hb, by omega, hn, (copies_two _ _).symm⟩

private def binom (n d : ℕ) : ℚ := (2 * n + d).choose n

private def correction (n : ℕ) : ℚ := if n % 2 = 0 then binom (n / 2) 1 else 0

private lemma count (n : ℕ) : (term n : ℚ) = binom n 2 - correction n := by
  let blocks := ((range (n + 1)).powersetCard (n / 2)).filter (fun _ => n % 2 = 0)
  have mem_blocks (b : Finset ℕ) : b ∈ blocks ↔ b ⊆ range (n + 1) ∧ n = 2 * b.card := by
    simp only [blocks, mem_filter, mem_powersetCard]
    grind
  have bij : blocks.card = ((words n).filter (repeated n)).card := by
    apply card_nbij (double (n + 1))
    · intro b hb
      obtain ⟨hs, hc⟩ := (mem_blocks b).mp hb
      have bounded : ∀ i ∈ b, i < n + 1 := by simpa [Finset.subset_iff] using hs
      have disj : Disjoint b (b.image (n + 1 + ·)) := by
        simp only [disjoint_left, mem_image]
        grind
      apply mem_filter.mpr
      refine ⟨mem_powersetCard.mpr ⟨?_, ?_⟩, periodic.mpr ⟨b, hs, hc, rfl⟩⟩
      · intro i hi
        simp only [double, mem_union, mem_image] at hi
        simp only [mem_range]
        grind
      · rw [double, card_union_of_disjoint disj, card_image_of_injective _ (add_right_injective _)]
        omega
    · intro b hb c hc he
      have lower (s : Finset ℕ) (hs : s ∈ blocks) : (double (n + 1) s) ∩ range (n + 1) = s := by
        have bounded := ((mem_blocks _).mp hs).1
        ext i
        simp only [double, mem_inter, mem_union, mem_image, mem_range]
        grind
      rw [← lower b hb, he, lower c hc]
    · intro w hw
      obtain ⟨b, hb, hc, he⟩ := periodic.mp (mem_filter.mp hw).2
      exact ⟨b, (mem_blocks _).mpr ⟨hb, hc⟩, he⟩
  have partition := card_filter_add_card_filter_not (s := words n) (repeated n)
  change _ + term n = _ at partition
  rw [← bij] at partition
  by_cases h : n % 2 = 0
  · have index : 2 * (n / 2) + 1 = n + 1 := by omega
    simp [blocks, h, words, card_powersetCard] at partition
    simp only [correction, h, if_true, binom, index, eq_sub_iff_add_eq]
    exact_mod_cast (add_comm _ _).trans partition
  · simp [blocks, h, words, card_powersetCard] at partition
    simp [correction, h, binom]
    exact_mod_cast partition

-- The ratio of successive binomial coefficients works for both offsets.
private lemma step (n d : ℕ) : binom (n + 1) d =
    ((2 * (n : ℚ) + d + 2) * (2 * n + d + 1)) / ((n + 1) * (n + d + 1)) * binom n d := by
  unfold binom
  rw [Nat.cast_choose ℚ (show n + 1 ≤ 2 * (n + 1) + d by omega),
    Nat.cast_choose ℚ (show n ≤ 2 * n + d by omega),
    show 2 * (n + 1) + d - (n + 1) = (n + d) + 1 by omega, show 2 * n + d - n = n + d by omega,
    show 2 * (n + 1) + d = (2 * n + d) + 1 + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

private lemma correction_step (n : ℕ) : correction (n + 2) =
    4 * ((n : ℚ) + 3) / (n + 4) * correction n := by
  obtain ⟨k, rfl | rfl⟩ := n.even_or_odd'
  · simp only [correction, show (2 * k + 2) % 2 = 0 by omega, show (2 * k) % 2 = 0 by omega, if_true,
      show (2 * k + 2) / 2 = k + 1 by omega, show (2 * k) / 2 = k by omega, step k 1]
    push_cast
    field_simp
    ring
  · simp [correction]

end OMA.S_oeis_a051195

open OMA.S_oeis_a051195

theorem OMA.solution : type_of% @OMA.S_oeis_a051195.main := by
  intro k
  simp only [count, recurrence, step (k + 3) 2, step (k + 2) 2, step (k + 1) 2, step k 2,
    correction_step (k + 2), correction_step (k + 1), correction_step k]
  push_cast
  field_simp
  ring
