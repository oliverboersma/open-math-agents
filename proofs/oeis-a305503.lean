import OMAStatements.S_oeis_a305503

/-! The middle of a nearly full interval contributes every sum and difference.
Only the fringes need a finite comparison. -/

open Finset
open scoped Pointwise

namespace OMA.A305503

private noncomputable def holes (N : ℤ) (A : Finset ℤ) : Finset ℤ := Icc 0 N \ A

private theorem avoidTwo (H I : Finset ℤ) (f g : ℤ → ℤ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (h : 2 * H.card < I.card) :
    ∃ i ∈ I, f i ∉ H ∧ g i ∉ H := by
  by_contra! hn
  let F := I.filter (fun i => f i ∈ H)
  let G := I.filter (fun i => g i ∈ H)
  have hF : F.card ≤ H.card :=
    card_le_card_of_injOn f (fun i hi => (mem_filter.mp hi).2) hf.injOn
  have hG : G.card ≤ H.card :=
    card_le_card_of_injOn g (fun i hi => (mem_filter.mp hi).2) hg.injOn
  have hI : I ⊆ F ∪ G := by
    intro i hi
    by_cases hfi : f i ∈ H
    · exact mem_union_left _ (mem_filter.mpr ⟨hi, hfi⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hi, hn i hi hfi⟩)
  have hh := (card_le_card hI).trans (card_union_le F G)
  omega

private theorem avoidDisjointPairs (H I : Finset ℤ) (f g : ℤ → ℤ)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hcross : ∀ i ∈ I, ∀ j ∈ I, f i = g j → i = j)
    (h : H.card < I.card) :
    ∃ i ∈ I, f i ∉ H ∧ g i ∉ H := by
  by_contra! hn
  let pick (i : ℤ) := if f i ∈ H then f i else g i
  have hmem : Set.MapsTo pick (I : Set ℤ) (H : Set ℤ) := by
    intro i hi
    change i ∈ I at hi
    change pick i ∈ H
    by_cases hfi : f i ∈ H
    · simp [pick, hfi]
    · simpa [pick, hfi] using hn i hi hfi
  have hinj : Set.InjOn pick (I : Set ℤ) := by
    intro i hi j hj hij
    by_cases hfi : f i ∈ H <;> by_cases hfj : f j ∈ H <;>
      simp only [pick, hfi, hfj, if_true, if_false] at hij
    · exact hf hij
    · exact hcross i hi j hj hij
    · exact (hcross j hj i hi hij.symm).symm
    · exact hg hij
  exact (not_le_of_gt h) (card_le_card_of_injOn pick hmem hinj)

private theorem mem_of_not_hole {N x : ℤ} {A : Finset ℤ}
    (h₀ : 0 ≤ x) (hN : x ≤ N) (h : x ∉ holes N A) : x ∈ A := by
  by_contra hn
  exact h (mem_sdiff.mpr ⟨mem_Icc.mpr ⟨h₀, hN⟩, hn⟩)

private theorem middleSum {N x : ℤ} {A : Finset ℤ}
    (h : (holes N A).card ≤ 6) (hx : 12 ≤ x) (hx' : x ≤ 2 * N - 12) :
    x ∈ A + A := by
  let I := Icc (max 0 (x - N)) (x / 2)
  have hc : 6 < I.card := by
    dsimp [I]
    rw [Int.card_Icc]
    by_cases hw : x - N ≤ 0
    · rw [max_eq_left hw]
      omega
    · rw [max_eq_right (by omega : 0 ≤ x - N)]
      omega
  obtain ⟨i, hi, hf, hg⟩ := avoidDisjointPairs (holes N A) I id (fun i => x - i)
    (fun _ _ h => h) (by intro i j hj; change x - i = x - j at hj; omega)
    (by
      intro i hi j hj hij
      have hi' := (mem_Icc.mp hi).2
      have hj' := (mem_Icc.mp hj).2
      change i = x - j at hij
      omega)
    (h.trans_lt hc)
  obtain ⟨hi₀, hi₁⟩ := mem_Icc.mp hi
  change max 0 (x - N) ≤ i at hi₀
  refine mem_add.mpr ⟨i, mem_of_not_hole ?_ ?_ hf, x - i,
    mem_of_not_hole ?_ ?_ hg, by omega⟩ <;>
    have hzero := (le_max_left 0 (x - N)).trans hi₀ <;>
    have hleft := (le_max_right 0 (x - N)).trans hi₀ <;> omega

private theorem middleDiff {N d : ℤ} {A : Finset ℤ}
    (hN : 24 ≤ N) (h : (holes N A).card ≤ 6) (hd : 1 ≤ d) (hd' : d ≤ N - 6) :
    d ∈ A - A := by
  let I := Icc 0 (N - d)
  have hc : I.card = (N - d + 1).toNat := by simp [I, Int.card_Icc]
  have hp : ∃ i ∈ I, i ∉ holes N A ∧ i + d ∉ holes N A := by
    by_cases hsplit : N < 2 * d
    · apply avoidDisjointPairs (holes N A) I id (fun i => i + d)
        (fun _ _ h => h) (by intro i j hj; change i + d = j + d at hj; omega) _ (by rw [hc]; omega)
      intro i hi j hj hij
      have hi' := (mem_Icc.mp hi).2
      have hj' := (mem_Icc.mp hj).1
      change i = j + d at hij
      omega
    · exact avoidTwo (holes N A) I id (fun i => i + d)
        (fun _ _ h => h) (by intro i j hj; change i + d = j + d at hj; omega) (by rw [hc]; omega)
  obtain ⟨i, hi, ha, hb⟩ := hp
  obtain ⟨hi₀, hi₁⟩ := mem_Icc.mp hi
  exact mem_sub.mpr ⟨i + d, mem_of_not_hole (by omega) (by omega) hb,
    i, mem_of_not_hole hi₀ (by omega) ha, by omega⟩

private noncomputable def sumMissing (N : ℤ) (A : Finset ℤ) := Icc 0 (2 * N) \ (A + A)

private noncomputable def posMissing (N : ℤ) (A : Finset ℤ) := Icc 1 N \ (A - A)

private theorem sum_card {N : ℤ} {A : Finset ℤ} (hA : A ⊆ Icc 0 N) :
    (sumMissing N A).card + (A + A).card = (2 * N + 1).toNat := by
  unfold sumMissing
  rw [card_sdiff_add_card_eq_card, Int.card_Icc]
  · simp
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hx
  obtain ⟨ha₀, ha₁⟩ := mem_Icc.mp (hA ha)
  obtain ⟨hb₀, hb₁⟩ := mem_Icc.mp (hA hb)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

private theorem diff_card {N : ℤ} {A : Finset ℤ} (hA : A ⊆ Icc 0 N)
    (hn : A.Nonempty) :
    2 * (posMissing N A).card + (A - A).card = (2 * N + 1).toNat := by
  have hsub : A - A ⊆ Icc (-N) N := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.mp hx
    obtain ⟨ha₀, ha₁⟩ := mem_Icc.mp (hA ha)
    obtain ⟨hb₀, hb₁⟩ := mem_Icc.mp (hA hb)
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  have symm (x : ℤ) : -x ∈ A - A ↔ x ∈ A - A := by
    constructor <;> intro hx <;> obtain ⟨a, ha, b, hb, hh⟩ := mem_sub.mp hx <;>
      exact mem_sub.mpr ⟨b, hb, a, ha, by omega⟩
  have hz : 0 ∈ A - A := by
    obtain ⟨a, ha⟩ := hn
    exact mem_sub.mpr ⟨a, ha, a, ha, sub_self a⟩
  let P := posMissing N A
  have hd : Disjoint P (P.image Neg.neg) := by
    refine disjoint_left.mpr fun x hx hi => ?_
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hi
    have hpos₁ := (mem_Icc.mp (mem_sdiff.mp hx).1).1
    have hpos₂ := (mem_Icc.mp (mem_sdiff.mp hy).1).1
    omega
  have heq : Icc (-N) N \ (A - A) = P ∪ P.image Neg.neg := by
    ext x
    simp only [P, posMissing, mem_sdiff, mem_Icc, mem_union, mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hx⟩
      by_cases h : 1 ≤ x
      · exact Or.inl ⟨⟨h, hhi⟩, hx⟩
      · have hnz : x ≠ 0 := fun he => hx (he ▸ hz)
        exact Or.inr ⟨-x, ⟨⟨by omega, by omega⟩, fun h' => hx ((symm x).mp h')⟩, by omega⟩
    · rintro (⟨⟨hlo, hhi⟩, hx⟩ | ⟨y, ⟨⟨hlo, hhi⟩, hy⟩, rfl⟩)
      · exact ⟨⟨by omega, hhi⟩, hx⟩
      · exact ⟨⟨by omega, by omega⟩, fun h' => hy ((symm y).mp h')⟩
  have hcard := card_sdiff_add_card_eq_card hsub
  rw [heq, card_union_of_disjoint hd, card_image_of_injective _ neg_injective, Int.card_Icc] at hcard
  change (posMissing N A).card + (posMissing N A).card + (A - A).card = _ at hcard
  omega

private theorem more_sums_iff {N : ℤ} {A : Finset ℤ} (hA : A ⊆ Icc 0 N)
    (hn : A.Nonempty) :
    (A - A).card < (A + A).card ↔ (sumMissing N A).card < 2 * (posMissing N A).card := by
  have hs := sum_card hA
  have hd := diff_card hA hn
  omega

private theorem holes_card {N : ℤ} {A : Finset ℤ} (hA : A ⊆ Icc 0 N) :
    (holes N A).card + A.card = (N + 1).toNat := by
  unfold holes
  rw [card_sdiff_add_card_eq_card hA, Int.card_Icc]
  simp

private def deleted (N : ℤ) : Finset ℤ := {1, 4, 5, 6, N - 6, N - 4, N - 3}

private noncomputable def witness (N : ℤ) : Finset ℤ := Icc 0 N \ deleted N

private theorem witness_card {N : ℤ} (hN : 16 ≤ N) : (witness N).card = (N - 6).toNat := by
  have hd : deleted N ⊆ Icc 0 N := by
    intro i hi
    simp only [deleted, mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact mem_Icc.mpr ⟨by omega, by omega⟩
  have hcard : (deleted N).card = 7 := by
    unfold deleted
    repeat' rw [card_insert_of_notMem (by simp only [mem_insert, mem_singleton]; omega)]
    rfl
  have h := card_sdiff_add_card_eq_card hd
  change (witness N).card + (deleted N).card = _ at h
  rw [hcard, Int.card_Icc] at h
  omega

private theorem witness_mem {N i : ℤ} (hN : 17 ≤ N) :
    i ∈ witness N ↔ i ∈ ({0, 2, 3} : Finset ℤ) ∨ (7 ≤ i ∧ i ≤ N - 7) ∨
      N - i ∈ ({0, 1, 2, 5} : Finset ℤ) := by
  simp only [witness, deleted, mem_sdiff, mem_Icc, mem_insert, mem_singleton]
  omega

set_option maxHeartbeats 1000000 in
private theorem witness_sum {N x : ℤ} (hN : 17 ≤ N)
    (h₀ : 0 ≤ x) (h₁ : x ≤ 2 * N) (hne : x ≠ 1) : x ∈ witness N + witness N := by
  have make (a b : ℤ) (ha : a ∈ witness N) (hb : b ∈ witness N) (h : a + b = x) :
      x ∈ witness N + witness N := mem_add.mpr ⟨a, ha, b, hb, h⟩
  have L (a : ℤ) (h : a ∈ ({0, 2, 3} : Finset ℤ)) : a ∈ witness N :=
    (witness_mem hN).mpr (Or.inl h)
  have R (a : ℤ) (h : a ∈ ({0, 1, 2, 5} : Finset ℤ)) : N - a ∈ witness N :=
    (witness_mem hN).mpr (Or.inr (Or.inr (by simpa using h)))
  have M (a : ℤ) (ha : 7 ≤ a) (hb : a ≤ N - 7) : a ∈ witness N :=
    (witness_mem hN).mpr (Or.inr (Or.inl ⟨ha, hb⟩))
  by_cases hx : x ≤ 6
  · have pairs : ∀ j : Fin 7, j.val ≠ 1 → ∃ a b : Fin 4,
        (a.val = 0 ∨ a.val = 2 ∨ a.val = 3) ∧
        (b.val = 0 ∨ b.val = 2 ∨ b.val = 3) ∧ a.val + b.val = j.val := by decide
    let j : Fin 7 := ⟨x.toNat, by omega⟩
    have hj : j.val = x.toNat := rfl
    obtain ⟨a, b, ha, hb, he⟩ := pairs j (by omega)
    exact make (a.val : ℤ) (b.val : ℤ) (L _ (by simp only [mem_insert, mem_singleton]; omega))
      (L _ (by simp only [mem_insert, mem_singleton]; omega)) (by omega)
  by_cases hy : 2 * N - 6 ≤ x
  · have pairs : ∀ j : Fin 7, ∃ a b : Fin 6,
        (a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 5) ∧
        (b.val = 0 ∨ b.val = 1 ∨ b.val = 2 ∨ b.val = 5) ∧ a.val + b.val = j.val := by decide
    let j : Fin 7 := ⟨(2 * N - x).toNat, by omega⟩
    have hj : j.val = (2 * N - x).toNat := rfl
    obtain ⟨a, b, ha, hb, he⟩ := pairs j
    exact make (N - a.val) (N - b.val) (R _ (by simp only [mem_insert, mem_singleton]; omega))
      (R _ (by simp only [mem_insert, mem_singleton]; omega)) (by omega)
  by_cases hz : x ≤ N - 4
  · by_cases hs : x ≤ N - 7
    · exact make 0 x (L _ (by simp)) (M _ (by omega) hs) (by omega)
    · exact make 3 (x - 3) (L _ (by simp)) (M _ (by omega) (by omega)) (by omega)
  by_cases hw : N + 2 ≤ x
  · by_cases ht : N + 7 ≤ x
    · exact make (N - 0) (x - N) (R 0 (by simp)) (M (x - N) (by omega) (by omega)) (by omega)
    · by_cases hm : x ≤ N + 4
      · exact make (N - 5) (x - (N - 5)) (R 5 (by simp))
          (M (x - (N - 5)) (by omega) (by omega)) (by omega)
      · exact make (N - 2) (x - (N - 2)) (R 2 (by simp))
          (M (x - (N - 2)) (by omega) (by omega)) (by omega)
  · let a := max 7 (x - (N - 7))
    have hal : 7 ≤ a := le_max_left _ _
    have ham : x - (N - 7) ≤ a := le_max_right _ _
    have hau : a ≤ N - 7 := max_le (by omega) (by omega)
    have hax : a ≤ x - 7 := max_le (by omega) (by omega)
    exact make a (x - a) (M _ hal hau) (M _ (by omega) (by omega)) (by omega)

private theorem witness_good {N : ℤ} (hN : 17 ≤ N) :
    ((witness N) - (witness N)).card < ((witness N) + (witness N)).card := by
  have hsub : witness N ⊆ Icc 0 N := sdiff_subset
  have hn : (witness N).Nonempty := ⟨0, (witness_mem hN).mpr (Or.inl (by simp))⟩
  rw [more_sums_iff hsub hn]
  have hs : sumMissing N (witness N) ⊆ {1} := by
    intro x hx
    obtain ⟨hxi, hx⟩ := mem_sdiff.mp hx
    obtain ⟨hl, hu⟩ := mem_Icc.mp hxi
    exact mem_singleton.mpr (by_contra fun he => hx (witness_sum hN hl hu he))
  have hd : N - 6 ∈ posMissing N (witness N) := by
    refine mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    rintro hm
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sub.mp hm
    have hb₀ := mem_Icc.mp (hsub hb)
    have ha₀ := mem_Icc.mp (hsub ha)
    rw [witness_mem hN] at hb
    simp only [mem_insert, mem_singleton] at hb
    have he : a = N - 6 ∨ a = N - 4 ∨ a = N - 3 := by omega
    simp only [witness, deleted, mem_sdiff, mem_insert, mem_singleton] at ha
    omega
  have hsd := card_le_card hs
  rw [card_singleton] at hsd
  have hdd := card_pos.mpr ⟨_, hd⟩
  omega

private def encoded (n m : ℕ) : Finset ℤ :=
  ((range n).filter fun i => m.testBit i).image Int.ofNat

private theorem mem_encoded {n m : ℕ} {x : ℤ} :
    x ∈ encoded n m ↔ 0 ≤ x ∧ x < n ∧ m.testBit x.toNat = true := by
  simp only [encoded, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hm⟩, rfl⟩
    simpa using And.intro hi hm
  · rintro ⟨hx, hn, hm⟩
    exact ⟨x.toNat, ⟨by omega, hm⟩, Int.toNat_of_nonneg hx⟩

private def sumMask (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: rest => (if m.testBit i then m <<< i else 0) ||| sumMask m rest

private theorem testBit_sumMask (m s : ℕ) (l : List ℕ) :
    (sumMask m l).testBit s = true ↔
      ∃ a ∈ l, a ≤ s ∧ m.testBit a = true ∧ m.testBit (s - a) = true := by
  induction l with
  | nil => simp [sumMask]
  | cons i l ih =>
    rw [sumMask, Nat.testBit_or, Bool.or_eq_true, ih]
    by_cases h : m.testBit i = true
    · rw [if_pos h, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
      simp only [List.mem_cons]
      constructor
      · rintro (⟨hi, hs⟩ | ⟨j, hj, hg⟩)
        · exact ⟨i, Or.inl rfl, by omega, h, hs⟩
        · exact ⟨j, Or.inr hj, hg⟩
      · rintro ⟨j, (rfl | hj), hg⟩
        · exact Or.inl ⟨by omega, hg.2.2⟩
        · exact Or.inr ⟨j, hj, hg⟩
    · rw [if_neg h]
      have hz : (0 : ℕ).testBit s = false := by simp
      simp only [hz, Bool.false_eq_true, false_or, List.mem_cons]
      constructor
      · rintro ⟨j, hj, hg⟩
        exact ⟨j, Or.inr hj, hg⟩
      · rintro ⟨j, (rfl | hj), hg⟩
        · exact (h hg.2.1).elim
        · exact ⟨j, hj, hg⟩

private def pop (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => pop m n + (m.testBit n).toNat

-- Each four-bit entry of this table is the number of ones in the indexed byte.
private def byteCounts : ℕ := 0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110

private def countByte (m : ℕ) : ℕ := (byteCounts >>> (4 * (m % 256))) % 16

private def chunkCount (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | b+1 => countByte m + chunkCount (m >>> 8) b

private def fastPop (m n : ℕ) : ℕ := chunkCount (m % 2^n) ((n+7)/8)

private theorem pop_mod (m a b : ℕ) (hab : a ≤ b) : pop (m % 2^b) a = pop m a := by
  induction a with
  | zero => rfl
  | succ a ih =>
    rw [pop, pop, ih (by omega), Nat.testBit_mod_two_pow]
    simp [show a < b by omega]

private theorem pop_append (m a b : ℕ) : pop m (a+b) = pop m a + pop (m >>> a) b := by
  induction b with
  | zero => simp [pop]
  | succ b ih =>
    rw [← Nat.add_assoc, pop, pop, ih, Nat.testBit_shiftRight, Nat.add_assoc]

set_option maxRecDepth 5000 in
private theorem countByte_eq (m : ℕ) : countByte m = pop m 8 := by
  have h : ∀ q : Fin 256, countByte q.val = pop q.val 8 := by decide +kernel
  have hp := pop_mod m 8 8 le_rfl
  rw [show (2 : ℕ)^8 = 256 by decide] at hp
  calc
    countByte m = countByte (m % 256) := by unfold countByte; rw [Nat.mod_mod]
    _ = pop (m % 256) 8 := h ⟨m % 256, Nat.mod_lt _ (by decide)⟩
    _ = pop m 8 := hp

private theorem chunkCount_eq (m b : ℕ) : chunkCount m b = pop m (8*b) := by
  induction b generalizing m with
  | zero => rfl
  | succ b ih =>
    rw [chunkCount, countByte_eq, ih, show 8 * (b+1) = 8 + 8*b by omega, pop_append]

private theorem fastPop_eq (m n : ℕ) : fastPop m n = pop m n := by
  unfold fastPop
  rw [chunkCount_eq]
  let b := 8 * ((n+7)/8) - n
  have he : 8 * ((n+7)/8) = n + b := by dsimp [b]; omega
  rw [he]
  have hr (k : ℕ) : pop (m % 2^n) (n+k) = pop (m % 2^n) n := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, pop, ih, Nat.testBit_lt_two_pow, Bool.toNat_false, Nat.add_zero]
      exact (Nat.mod_lt _ (Nat.two_pow_pos n)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  rw [hr, pop_mod _ n n le_rfl]

private theorem card_encoded (n m : ℕ) : (encoded n m).card = pop m n := by
  rw [encoded, card_image_of_injective _ Int.ofNat_injective]
  induction n with
  | zero => simp [pop]
  | succ n ih =>
    rw [range_add_one, filter_insert, pop]
    have hn : n ∉ (range n).filter (fun i => m.testBit i) := fun h =>
      (Nat.lt_irrefl n) (mem_range.mp (mem_filter.mp h).1)
    cases m.testBit n
    · simp [ih]
    · simp [card_insert_of_notMem hn, ih]

private def pairMask (m d : ℕ) := m &&& (m >>> d)

private theorem mem_pairMask {n m d : ℕ} {i : ℤ} (hd : d ≤ n) :
    i ∈ encoded (n - d) (pairMask m d) ↔
      i ∈ encoded n m ∧ i + d ∈ encoded n m := by
  simp only [mem_encoded, pairMask, Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true]
  constructor
  · rintro ⟨hi, hn, h₀, h₁⟩
    have ht : (i + (d : ℤ)).toNat = d + i.toNat := by omega
    exact ⟨⟨hi, by omega, h₀⟩, ⟨by omega, by omega, ht ▸ h₁⟩⟩
  · rintro ⟨⟨hi, hn, h₀⟩, ⟨_, hd', h₁⟩⟩
    have ht : (i + (d : ℤ)).toNat = d + i.toNat := by omega
    exact ⟨hi, by omega, h₀, ht ▸ h₁⟩

private theorem sum_le_pop {n m : ℕ} {N : ℤ} {A : Finset ℤ} (hn : (n : ℤ) = N + 1)
    (hsub : A ⊆ encoded n m) :
    (A + A).card ≤ pop (sumMask m (List.range n)) (2 * n - 1) := by
  rw [← card_encoded]
  apply card_le_card
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hx
  obtain ⟨ha₀, ha₁, hm₀⟩ := mem_encoded.mp (hsub ha)
  obtain ⟨hb₀, hb₁, hm₁⟩ := mem_encoded.mp (hsub hb)
  refine mem_encoded.mpr ⟨by omega, by omega, (testBit_sumMask _ _ _).mpr ?_⟩
  exact ⟨a.toNat, List.mem_range.mpr (by omega), by omega, hm₀,
    by rwa [show (a + b).toNat - a.toNat = b.toNat by omega]⟩

private def candidateDiffs (n : ℕ) : Finset ℕ :=
  Ico (n - 6) n ∪ (if n = 16 then {5,6} else if n ≤ 18 then {6} else ∅)

private theorem candidate_diff {n d : ℕ} {N : ℤ} {A : Finset ℤ}
    (hn : (n : ℤ) = N + 1) (h16 : 16 ≤ n) (h : (holes N A).card ≤ 6)
    (hd : 0 < d) (hd' : d < n) (hmiss : (d : ℤ) ∉ A - A) :
    d ∈ candidateDiffs n := by
  by_contra hm
  have near : d < n - 6 := by
    by_contra! he
    exact hm (mem_union_left _ (mem_Ico.mpr ⟨he,hd'⟩))
  have small (I : Finset ℤ) (hi : ∀ i ∈ I, 0 ≤ i ∧ i + (d : ℤ) ≤ N)
      (hI : 6 < I.card)
      (hcross : ∀ i ∈ I, ∀ j ∈ I, i = j + (d : ℤ) → i = j) : False := by
    obtain ⟨i, hi', notL, notR⟩ := avoidDisjointPairs (holes N A) I id (· + (d : ℤ))
      (fun _ _ e => e) (fun _ _ e => add_right_cancel e) hcross (h.trans_lt hI)
    obtain ⟨hlo, hhi⟩ := hi i hi'
    exact hmiss (mem_sub.mpr ⟨_, mem_of_not_hole (by omega) hhi notR,
      i, mem_of_not_hole hlo (by omega) notL, by omega⟩)
  by_cases hl : 7 ≤ d
  · refine small (Icc 0 6) (fun i hi => ?_) (by decide) ?_
    · obtain ⟨hlo, hhi⟩ := mem_Icc.mp hi
      omega
    · intro i hi j hj he
      have hi' := mem_Icc.mp hi
      have hj' := mem_Icc.mp hj
      omega
  · by_cases hfar : 12 ≤ N - (d : ℤ)
    · let I := Icc 0 (N - (d : ℤ))
      have hc : 2 * (holes N A).card < I.card := by
        dsimp [I]
        rw [Int.card_Icc]
        omega
      obtain ⟨i,hi,notL,notR⟩ := avoidTwo (holes N A) I id (· + (d : ℤ))
        (fun _ _ e => e) (fun _ _ e => add_right_cancel e) hc
      obtain ⟨hlo,hhi⟩ := mem_Icc.mp hi
      exact hmiss (mem_sub.mpr ⟨_, mem_of_not_hole (by omega) (by omega) notR,
        i, mem_of_not_hole hlo (by omega) notL, by omega⟩)
    · have possible : (n = 16 ∧ d = 4) ∨ (n = 17 ∧ d = 5) := by
        have excluded : ¬((n = 16 ∧ (d = 5 ∨ d = 6)) ∨ (n ≤ 18 ∧ d = 6)) := by
          rintro (⟨rfl, rfl | rfl⟩ | ⟨hle, rfl⟩)
          · exact hm (by decide)
          · exact hm (by decide)
          · apply hm
            apply mem_union_right
            by_cases he : n = 16
            · simp [he]
            · simp [he, hle]
        omega
      rcases possible with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · refine small {0,1,2,3,8,9,10} (fun i hi => ?_) (by decide) ?_
        · simp only [mem_insert, mem_singleton] at hi
          omega
        · intro i hi j hj he
          simp only [mem_insert, mem_singleton] at hi hj
          omega
      · refine small {0,1,2,3,4,10,11} (fun i hi => ?_) (by decide) ?_
        · simp only [mem_insert, mem_singleton] at hi
          omega
        · intro i hi j hj he
          simp only [mem_insert, mem_singleton] at hi hj
          omega

private def mightMiss (n present allowed k d : ℕ) : Bool :=
  ((pairMask present d) % 2^(n-d) == 0) &&
    decide (fastPop (pairMask allowed d) (n - d) ≤ if n ≤ 2 * d then k else 2 * k)

private def maybeMissing (n present allowed k : ℕ) : Finset ℕ :=
  (candidateDiffs n).filter (fun d => mightMiss n present allowed k d = true)

private def sufficient (n present allowed k : ℕ) : Bool :=
  let missing := (maybeMissing n present allowed k).card
  missing == 0 ||
    decide (fastPop (sumMask allowed (List.range n)) (2 * n - 1) + 2 * missing ≤ 2 * n - 1)

private theorem cert_sound {n present allowed k : ℕ} {N : ℤ} {A : Finset ℤ}
    (hn : (n : ℤ) = N + 1) (h16 : 16 ≤ n) (hA : A ⊆ Icc 0 N)
    (budget : (holes N A).card ≤ 6)
    (hP : encoded n present ⊆ A) (hE : A ⊆ encoded n allowed)
    (hK : (encoded n allowed \ A).card ≤ k)
    (h : sufficient n present allowed k = true) :
    2 * (posMissing N A).card ≤ (sumMissing N A).card := by
  have hd : (posMissing N A).card ≤ (maybeMissing n present allowed k).card := by
    apply card_le_card_of_injOn Int.toNat
    · intro x hx
      change x ∈ posMissing N A at hx
      obtain ⟨hxi, hmiss⟩ := mem_sdiff.mp hx
      obtain ⟨hx₀, hx₁⟩ := mem_Icc.mp hxi
      let d := x.toNat
      have hd' : d < n := by dsimp [d]; omega
      have he : (d : ℤ) = x := Int.toNat_of_nonneg (by omega)
      change d ∈ maybeMissing n present allowed k
      refine mem_filter.mpr ⟨candidate_diff hn h16 budget (by dsimp [d]; omega) hd'
        (by rwa [he]), ?_⟩
      simp only [mightMiss, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, fastPop_eq]
      constructor
      · apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
        by_cases hi : i < n - d
        · suffices (pairMask present d).testBit i = false by simp [hi, this]
          apply Bool.eq_false_iff.mpr
          intro hb
          have hp : (i : ℤ) ∈ encoded (n - d) (pairMask present d) :=
            mem_encoded.mpr ⟨by omega, by omega, by simpa using hb⟩
          obtain ⟨h₀, h₁⟩ := (mem_pairMask hd'.le).mp hp
          exact hmiss (mem_sub.mpr ⟨_, hP h₁, i, hP h₀, by omega⟩)
        · simp [hi]
      · rw [← card_encoded]
        let I := encoded (n - d) (pairMask allowed d)
        let H := encoded n allowed \ A
        change I.card ≤ _
        change H.card ≤ k at hK
        have hm (i : ℤ) (hi : i ∈ I) :
            i ∈ encoded n allowed ∧ i + (d : ℤ) ∈ encoded n allowed :=
          (mem_pairMask hd'.le).mp hi
        have hj : Function.Injective (fun i : ℤ => i + (d : ℤ)) := fun i j hij =>
          add_right_cancel hij
        have contradictPairs : (∃ i ∈ I, i ∉ H ∧ i + (d : ℤ) ∉ H) → False := by
          rintro ⟨i, hi, h₀, h₁⟩
          obtain ⟨hei, hedi⟩ := hm i hi
          have hai : i ∈ A := by_contra fun h' => h₀ (mem_sdiff.mpr ⟨hei, h'⟩)
          have hadi : i + (d : ℤ) ∈ A := by_contra fun h' => h₁ (mem_sdiff.mpr ⟨hedi, h'⟩)
          exact hmiss (mem_sub.mpr ⟨_, hadi, i, hai, by omega⟩)
        split
        · rename_i hn'
          by_contra! hlt
          apply contradictPairs
          apply avoidDisjointPairs H I id (fun i => i + (d : ℤ))
            (fun _ _ h => h) hj ?_ (hK.trans_lt hlt)
          intro i hi j hj hij
          obtain ⟨_, hi₁, _⟩ := mem_encoded.mp hi
          obtain ⟨hj₀, _, _⟩ := mem_encoded.mp hj
          change i = j + (d : ℤ) at hij
          omega
        · by_contra! hlt
          apply contradictPairs
          exact avoidTwo H I id (fun i => i + (d : ℤ)) (fun _ _ h => h) hj (by omega)
    · intro x hx y hy he
      have hx₀ := (mem_Icc.mp (mem_sdiff.mp (show x ∈ posMissing N A from hx)).1).1
      have hy₀ := (mem_Icc.mp (mem_sdiff.mp (show y ∈ posMissing N A from hy)).1).1
      omega
  simp only [sufficient, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, fastPop_eq] at h
  rcases h with h | h
  · omega
  · have hp := sum_le_pop hn hE
    have hs := sum_card hA
    omega

private def search (n : ℕ) : List ℕ → ℕ → ℕ → ℕ → Bool
  | [], present, allowed, k => sufficient n present allowed k
  | i :: rest, present, allowed, k =>
      if k = 0 then sufficient n allowed allowed 0
      else if sufficient n present allowed k then true
      else if allowed.testBit i = false ∨ n ≤ i then search n rest present allowed k
      else
        search n rest (present ||| 2^i) allowed k &&
          search n rest present (allowed ^^^ 2^i) (k - 1)

private theorem encoded_add_point {n m i : ℕ} {A : Finset ℤ}
    (hm : encoded n m ⊆ A) (hi : (i : ℤ) ∈ A) :
    encoded n (m ||| 2^i) ⊆ A := by
  intro x hx
  obtain ⟨h₀, h₁, hb⟩ := mem_encoded.mp hx
  rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq] at hb
  rcases hb with old | he
  · exact hm (mem_encoded.mpr ⟨h₀, h₁, old⟩)
  · rwa [show x = (i : ℤ) by omega]

private theorem encoded_remove_point {n m i : ℕ} (hi : (i : ℤ) ∈ encoded n m) :
    encoded n (m ^^^ 2^i) = (encoded n m).erase i := by
  have hbit : m.testBit i = true := by simpa using (mem_encoded.mp hi).2.2
  ext x
  simp only [mem_erase, mem_encoded, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : x.toNat = i
  · rw [h, hbit]
    simp only [decide_true, Bool.xor_self, Bool.false_eq_true, and_false]
    exact ⟨False.elim, by rintro ⟨hne, h₀, _, _⟩; exact hne (by omega)⟩
  · have he : i ≠ x.toNat := Ne.symm h
    simp only [he, decide_false, Bool.xor_false]
    constructor
    · rintro ⟨hx₀, hx₁, hb⟩
      exact ⟨by omega, hx₀, hx₁, hb⟩
    · rintro ⟨_, hx₀, hx₁, hb⟩
      exact ⟨hx₀, hx₁, hb⟩

private theorem search_sound {n : ℕ} {N : ℤ} {A : Finset ℤ}
    (hn : (n : ℤ) = N + 1) (h16 : 16 ≤ n) (hA : A ⊆ Icc 0 N)
    (budget : (holes N A).card ≤ 6) (l : List ℕ) {present allowed k : ℕ}
    (hP : encoded n present ⊆ A) (hE : A ⊆ encoded n allowed)
    (hK : (encoded n allowed \ A).card ≤ k)
    (h : search n l present allowed k = true) :
    2 * (posMissing N A).card ≤ (sumMissing N A).card := by
  induction l generalizing present allowed k with
  | nil => exact cert_sound hn h16 hA budget hP hE hK h
  | cons i rest ih =>
    rw [search] at h
    by_cases hk : k = 0
    · subst k
      rw [if_pos rfl] at h
      have he : encoded n allowed ⊆ A := by
        have ht : (encoded n allowed \ A).card = 0 := by omega
        exact sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp ht)
      exact cert_sound hn h16 hA budget he hE hK h
    · rw [if_neg hk] at h
      by_cases hs : sufficient n present allowed k = true
      · exact cert_sound hn h16 hA budget hP hE hK hs
      · rw [if_neg hs] at h
        split at h
        · exact ih hP hE hK h
        · rename_i hv
          have hi : (i : ℤ) ∈ encoded n allowed := by
            simp only [not_or, Bool.not_eq_false] at hv
            exact mem_encoded.mpr ⟨by omega, by omega, by simpa using hv.1⟩
          rw [Bool.and_eq_true] at h
          by_cases ha : (i : ℤ) ∈ A
          · exact ih (encoded_add_point hP ha) hE hK h.1
          · have he := encoded_remove_point hi
            have ht : (encoded n allowed).erase i \ A = (encoded n allowed \ A).erase i := by
              ext x
              simp only [mem_sdiff, mem_erase]
              tauto
            have hsub : A ⊆ encoded n (allowed ^^^ 2^i) := by
              rw [he]
              intro x hx
              exact mem_erase.mpr ⟨fun he => ha (he ▸ hx), hE hx⟩
            exact ih hP hsub
              (by rw [he, ht, card_erase_of_mem (mem_sdiff.mpr ⟨hi, ha⟩)]; omega) h.2

private def schedule (n : ℕ) : List ℕ :=
  (List.range (n / 2)).flatMap (fun i => [i, n - 1 - i]) ++
    (if n % 2 = 1 then [n / 2] else [])

private def finiteCheck (n : ℕ) : Bool :=
  search n (schedule n) 0 (2^n - 1) 6

/-- Retain the twelve positions at each end and fill the new middle position. -/
private noncomputable def compress (N : ℤ) (A : Finset ℤ) :=
  let F := (holes N A).filter (fun x => x ≤ 11 ∨ N - 11 ≤ x)
  Icc (0 : ℤ) 24 \ F.image (fun x => if x ≤ 11 then x else x + 24 - N)

private theorem compressed_holes (N : ℤ) (A : Finset ℤ) :
    (holes 24 (compress N A)).card ≤ (holes N A).card := by
  let F := (holes N A).filter (fun x => x ≤ 11 ∨ N - 11 ≤ x)
  let f (x : ℤ) := if x ≤ 11 then x else x + 24 - N
  have h : holes 24 (compress N A) ⊆ F.image f := by
    intro x hx
    obtain ⟨hx₀, hx₁⟩ := mem_sdiff.mp hx
    by_contra hp
    exact hx₁ (mem_sdiff.mpr ⟨hx₀, hp⟩)
  exact (card_le_card h).trans (card_image_le.trans (card_filter_le _ _))

private theorem compress_at {N x : ℤ} {A : Finset ℤ} (hN : 24 ≤ N)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ N) (hf : x ≤ 11 ∨ N - 11 ≤ x) :
    (if x ≤ 11 then x else x + 24 - N) ∈ compress N A ↔ x ∈ A := by
  let f (x : ℤ) := if x ≤ 11 then x else x + 24 - N
  have hinj (y : ℤ) (hy : y ≤ 11 ∨ N - 11 ≤ y) (he : f y = f x) : y = x := by
    dsimp [f] at he
    split at he <;> split at he <;> omega
  have hb : f x ∈ Icc 0 24 := by
    apply mem_Icc.mpr
    dsimp [f]
    split <;> omega
  constructor
  · intro hx
    by_contra hn
    exact (mem_sdiff.mp hx).2
      (mem_image.mpr ⟨x, mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hx₀,hx₁⟩,hn⟩,hf⟩,rfl⟩)
  · intro ha
    refine mem_sdiff.mpr ⟨hb, ?_⟩
    rintro hi
    obtain ⟨y, hy, he⟩ := mem_image.mp hi
    have hh := mem_filter.mp hy
    have eq := hinj y hh.2 he
    exact (mem_sdiff.mp hh.1).2 (eq ▸ ha)

private theorem compress_left {N x : ℤ} {A : Finset ℤ} (hN : 24 ≤ N)
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 11) : x ∈ compress N A ↔ x ∈ A := by
  simpa only [if_pos hx₁] using compress_at (A := A) hN hx₀ (by omega) (Or.inl hx₁)

private theorem compress_right {N x : ℤ} {A : Finset ℤ} (hN : 24 ≤ N)
    (hx₀ : N - 11 ≤ x) (hx₁ : x ≤ N) : x + 24 - N ∈ compress N A ↔ x ∈ A := by
  simpa only [if_neg (by omega : ¬x ≤ 11)] using
    compress_at (A := A) hN (by omega) hx₁ (Or.inr hx₀)

private theorem compress_counts {N : ℤ} {A : Finset ℤ} (hN : 24 ≤ N)
    (hA : A ⊆ Icc 0 N) (h : (holes N A).card ≤ 6) :
    (sumMissing N A).card = (sumMissing 24 (compress N A)).card ∧
    (posMissing N A).card = (posMissing 24 (compress N A)).card := by
  let B := compress N A
  have hB : B ⊆ Icc 0 24 := sdiff_subset
  have hholes := (compressed_holes N A).trans h
  have lo_sum {s : ℤ} (hs : s ≤ 11) : s ∈ B + B ↔ s ∈ A + A := by
    constructor
    · rintro hh
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hh
      obtain ⟨ha₀, _⟩ := mem_Icc.mp (hB ha)
      obtain ⟨hb₀, _⟩ := mem_Icc.mp (hB hb)
      exact mem_add.mpr ⟨a, (compress_left hN ha₀ (by omega)).mp ha,
        b, (compress_left hN hb₀ (by omega)).mp hb, rfl⟩
    · rintro hh
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hh
      obtain ⟨ha₀, _⟩ := mem_Icc.mp (hA ha)
      obtain ⟨hb₀, _⟩ := mem_Icc.mp (hA hb)
      exact mem_add.mpr ⟨a, (compress_left hN ha₀ (by omega)).mpr ha,
        b, (compress_left hN hb₀ (by omega)).mpr hb, rfl⟩
  have hi_sum {s : ℤ} (hs : 2 * N - 11 ≤ s) :
      s + 48 - 2 * N ∈ B + B ↔ s ∈ A + A := by
    constructor
    · rintro hh
      obtain ⟨a, ha, b, hb, he⟩ := mem_add.mp hh
      obtain ⟨_, ha₁⟩ := mem_Icc.mp (hB ha)
      obtain ⟨_, hb₁⟩ := mem_Icc.mp (hB hb)
      have h₁ := compress_right (A := A) hN (x := a + N - 24) (by omega) (by omega)
      have h₂ := compress_right (A := A) hN (x := b + N - 24) (by omega) (by omega)
      exact mem_add.mpr ⟨a + N - 24, h₁.mp (by convert ha using 1; omega),
        b + N - 24, h₂.mp (by convert hb using 1; omega), by omega⟩
    · rintro hh
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_add.mp hh
      obtain ⟨_, ha₁⟩ := mem_Icc.mp (hA ha)
      obtain ⟨_, hb₁⟩ := mem_Icc.mp (hA hb)
      exact mem_add.mpr ⟨a + 24 - N, (compress_right hN (by omega) ha₁).mpr ha,
        b + 24 - N, (compress_right hN (by omega) hb₁).mpr hb, by omega⟩
  have hi_diff {d : ℤ} (hd : N - 5 ≤ d) : d + 24 - N ∈ B - B ↔ d ∈ A - A := by
    constructor
    · rintro hh
      obtain ⟨a, ha, b, hb, he⟩ := mem_sub.mp hh
      obtain ⟨_, ha₁⟩ := mem_Icc.mp (hB ha)
      obtain ⟨hb₀, _⟩ := mem_Icc.mp (hB hb)
      have h₁ := compress_right (A := A) hN (x := a + N - 24) (by omega) (by omega)
      exact mem_sub.mpr ⟨a + N - 24, h₁.mp (by convert ha using 1; omega),
        b, (compress_left hN hb₀ (by omega)).mp hb, by omega⟩
    · rintro hh
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_sub.mp hh
      obtain ⟨_, ha₁⟩ := mem_Icc.mp (hA ha)
      obtain ⟨hb₀, _⟩ := mem_Icc.mp (hA hb)
      exact mem_sub.mpr ⟨a + 24 - N, (compress_right hN (by omega) ha₁).mpr ha,
        b, (compress_left hN hb₀ (by omega)).mpr hb, by omega⟩
  constructor
  · have fringe (s : ℤ) (hs : s ∈ sumMissing N A) : s ≤ 11 ∨ 2 * N - 11 ≤ s := by
      by_contra! hc
      exact (mem_sdiff.mp hs).2 (middleSum h (by omega) (by omega))
    have fringe' (s : ℤ) (hs : s ∈ sumMissing 24 B) : s ≤ 11 ∨ 37 ≤ s := by
      by_contra! hc
      exact (mem_sdiff.mp hs).2 (middleSum hholes (by omega) (by omega))
    apply card_bij' (fun s _ => if s ≤ 11 then s else s + 48 - 2 * N)
      (fun s _ => if s ≤ 11 then s else s - 48 + 2 * N)
    · intro s hs
      obtain ⟨⟨hl, hu⟩, hm⟩ := And.intro (mem_Icc.mp (mem_sdiff.mp hs).1) (mem_sdiff.mp hs).2
      split
      · rename_i hc
        exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hl, by omega⟩, fun he => hm ((lo_sum hc).mp he)⟩
      · rename_i hc
        have hf := fringe s hs
        exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
          fun he => hm ((hi_sum (by omega)).mp he)⟩
    · intro s hs
      obtain ⟨⟨hl, hu⟩, hm⟩ := And.intro (mem_Icc.mp (mem_sdiff.mp hs).1) (mem_sdiff.mp hs).2
      split
      · rename_i hc
        exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨hl, by omega⟩, fun he => hm ((lo_sum hc).mpr he)⟩
      · have hf := fringe' s hs
        refine mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        intro he
        have hh := (hi_sum (s := s - 48 + 2 * N) (by omega)).mpr he
        exact hm (by convert hh using 1; omega)
    · intro s hs
      have hf := fringe s hs
      split <;> (try split) <;> omega
    · intro s hs
      have hf := fringe' s hs
      split <;> (try split) <;> omega
  · apply card_bij' (fun d _ => d + 24 - N) (fun d _ => d - 24 + N)
    · intro d hd
      obtain ⟨⟨hl, hu⟩, hm⟩ := And.intro (mem_Icc.mp (mem_sdiff.mp hd).1) (mem_sdiff.mp hd).2
      have hf : N - 5 ≤ d := by
        by_contra! hh
        exact hm (middleDiff hN h hl (by omega))
      exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, fun hs => hm ((hi_diff hf).mp hs)⟩
    · intro d hd
      obtain ⟨⟨hl, hu⟩, hm⟩ := And.intro (mem_Icc.mp (mem_sdiff.mp hd).1) (mem_sdiff.mp hd).2
      have hf : 19 ≤ d := by
        by_contra! hh
        exact hm (middleDiff (by decide : (24 : ℤ) ≤ 24) hholes hl (by omega))
      refine mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
      intro he
      have hh := (hi_diff (d := d - 24 + N) (by omega)).mpr he
      exact hm (by convert hh using 1; omega)
    · intro d hd
      omega
    · intro d hd
      omega

private theorem search_step {n i present allowed k : ℕ} {rest : List ℕ}
    (hk : k ≠ 0) (hv : ¬(allowed.testBit i = false ∨ n ≤ i))
    (left : search n rest (present ||| 2^i) allowed k = true)
    (right : search n rest present (allowed ^^^ 2^i) (k - 1) = true) :
    search n (i :: rest) present allowed k = true := by
  simp only [search, if_neg hk]
  split
  · rfl
  · simp only [left, right, Bool.and_self]

-- Each small block certifies the continuations of one partial assignment.
set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_1111 :
    search 16 ((schedule 16).drop 4) 49155 65535 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_1110 :
    search 16 ((schedule 16).drop 4) 32771 49151 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_1101 :
    search 16 ((schedule 16).drop 4) 49153 65533 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_1100 :
    search 16 ((schedule 16).drop 4) 32769 49149 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_1011 :
    search 16 ((schedule 16).drop 4) 16387 32767 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_1010 :
    search 16 ((schedule 16).drop 4) 3 16383 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_1001 :
    search 16 ((schedule 16).drop 4) 16385 32765 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_1000 :
    search 16 ((schedule 16).drop 4) 1 16381 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_0111 :
    search 16 ((schedule 16).drop 4) 49154 65534 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_0110 :
    search 16 ((schedule 16).drop 4) 32770 49150 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_0101 :
    search 16 ((schedule 16).drop 4) 49152 65532 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_0100 :
    search 16 ((schedule 16).drop 4) 32768 49148 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_0011 :
    search 16 ((schedule 16).drop 4) 16386 32766 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_0010 :
    search 16 ((schedule 16).drop 4) 2 16382 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_0001 :
    search 16 ((schedule 16).drop 4) 16384 32764 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_16_0000 :
    search 16 ((schedule 16).drop 4) 0 16380 2 = true := by decide +kernel

private theorem cert16 : finiteCheck 16 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_16_1111 finite_16_1110) (search_step (by decide) (by decide) finite_16_1101 finite_16_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_16_1011 finite_16_1010) (search_step (by decide) (by decide) finite_16_1001 finite_16_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_16_0111 finite_16_0110) (search_step (by decide) (by decide) finite_16_0101 finite_16_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_16_0011 finite_16_0010) (search_step (by decide) (by decide) finite_16_0001 finite_16_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_1111 :
    search 17 ((schedule 17).drop 4) 98307 131071 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_1110 :
    search 17 ((schedule 17).drop 4) 65539 98303 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_1101 :
    search 17 ((schedule 17).drop 4) 98305 131069 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_1100 :
    search 17 ((schedule 17).drop 4) 65537 98301 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_1011 :
    search 17 ((schedule 17).drop 4) 32771 65535 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_1010 :
    search 17 ((schedule 17).drop 4) 3 32767 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_1001 :
    search 17 ((schedule 17).drop 4) 32769 65533 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_1000 :
    search 17 ((schedule 17).drop 4) 1 32765 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_0111 :
    search 17 ((schedule 17).drop 4) 98306 131070 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_0110 :
    search 17 ((schedule 17).drop 4) 65538 98302 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_0101 :
    search 17 ((schedule 17).drop 4) 98304 131068 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_0100 :
    search 17 ((schedule 17).drop 4) 65536 98300 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_0011 :
    search 17 ((schedule 17).drop 4) 32770 65534 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_0010 :
    search 17 ((schedule 17).drop 4) 2 32766 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_0001 :
    search 17 ((schedule 17).drop 4) 32768 65532 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_17_0000 :
    search 17 ((schedule 17).drop 4) 0 32764 2 = true := by decide +kernel

private theorem cert17 : finiteCheck 17 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_17_1111 finite_17_1110) (search_step (by decide) (by decide) finite_17_1101 finite_17_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_17_1011 finite_17_1010) (search_step (by decide) (by decide) finite_17_1001 finite_17_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_17_0111 finite_17_0110) (search_step (by decide) (by decide) finite_17_0101 finite_17_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_17_0011 finite_17_0010) (search_step (by decide) (by decide) finite_17_0001 finite_17_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_1111 :
    search 18 ((schedule 18).drop 4) 196611 262143 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_1110 :
    search 18 ((schedule 18).drop 4) 131075 196607 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_1101 :
    search 18 ((schedule 18).drop 4) 196609 262141 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_1100 :
    search 18 ((schedule 18).drop 4) 131073 196605 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_1011 :
    search 18 ((schedule 18).drop 4) 65539 131071 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_1010 :
    search 18 ((schedule 18).drop 4) 3 65535 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_1001 :
    search 18 ((schedule 18).drop 4) 65537 131069 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_1000 :
    search 18 ((schedule 18).drop 4) 1 65533 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_0111 :
    search 18 ((schedule 18).drop 4) 196610 262142 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_0110 :
    search 18 ((schedule 18).drop 4) 131074 196606 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_0101 :
    search 18 ((schedule 18).drop 4) 196608 262140 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_0100 :
    search 18 ((schedule 18).drop 4) 131072 196604 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_0011 :
    search 18 ((schedule 18).drop 4) 65538 131070 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_0010 :
    search 18 ((schedule 18).drop 4) 2 65534 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_0001 :
    search 18 ((schedule 18).drop 4) 65536 131068 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_18_0000 :
    search 18 ((schedule 18).drop 4) 0 65532 2 = true := by decide +kernel

private theorem cert18 : finiteCheck 18 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_18_1111 finite_18_1110) (search_step (by decide) (by decide) finite_18_1101 finite_18_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_18_1011 finite_18_1010) (search_step (by decide) (by decide) finite_18_1001 finite_18_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_18_0111 finite_18_0110) (search_step (by decide) (by decide) finite_18_0101 finite_18_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_18_0011 finite_18_0010) (search_step (by decide) (by decide) finite_18_0001 finite_18_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_1111 :
    search 19 ((schedule 19).drop 4) 393219 524287 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_1110 :
    search 19 ((schedule 19).drop 4) 262147 393215 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_1101 :
    search 19 ((schedule 19).drop 4) 393217 524285 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_1100 :
    search 19 ((schedule 19).drop 4) 262145 393213 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_1011 :
    search 19 ((schedule 19).drop 4) 131075 262143 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_1010 :
    search 19 ((schedule 19).drop 4) 3 131071 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_1001 :
    search 19 ((schedule 19).drop 4) 131073 262141 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_1000 :
    search 19 ((schedule 19).drop 4) 1 131069 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_0111 :
    search 19 ((schedule 19).drop 4) 393218 524286 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_0110 :
    search 19 ((schedule 19).drop 4) 262146 393214 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_0101 :
    search 19 ((schedule 19).drop 4) 393216 524284 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_0100 :
    search 19 ((schedule 19).drop 4) 262144 393212 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_0011 :
    search 19 ((schedule 19).drop 4) 131074 262142 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_0010 :
    search 19 ((schedule 19).drop 4) 2 131070 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_0001 :
    search 19 ((schedule 19).drop 4) 131072 262140 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_19_0000 :
    search 19 ((schedule 19).drop 4) 0 131068 2 = true := by decide +kernel

private theorem cert19 : finiteCheck 19 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_19_1111 finite_19_1110) (search_step (by decide) (by decide) finite_19_1101 finite_19_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_19_1011 finite_19_1010) (search_step (by decide) (by decide) finite_19_1001 finite_19_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_19_0111 finite_19_0110) (search_step (by decide) (by decide) finite_19_0101 finite_19_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_19_0011 finite_19_0010) (search_step (by decide) (by decide) finite_19_0001 finite_19_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_1111 :
    search 20 ((schedule 20).drop 4) 786435 1048575 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_1110 :
    search 20 ((schedule 20).drop 4) 524291 786431 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_1101 :
    search 20 ((schedule 20).drop 4) 786433 1048573 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_1100 :
    search 20 ((schedule 20).drop 4) 524289 786429 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_1011 :
    search 20 ((schedule 20).drop 4) 262147 524287 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_1010 :
    search 20 ((schedule 20).drop 4) 3 262143 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_1001 :
    search 20 ((schedule 20).drop 4) 262145 524285 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_1000 :
    search 20 ((schedule 20).drop 4) 1 262141 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_0111 :
    search 20 ((schedule 20).drop 4) 786434 1048574 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_0110 :
    search 20 ((schedule 20).drop 4) 524290 786430 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_0101 :
    search 20 ((schedule 20).drop 4) 786432 1048572 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_0100 :
    search 20 ((schedule 20).drop 4) 524288 786428 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_0011 :
    search 20 ((schedule 20).drop 4) 262146 524286 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_0010 :
    search 20 ((schedule 20).drop 4) 2 262142 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_0001 :
    search 20 ((schedule 20).drop 4) 262144 524284 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_20_0000 :
    search 20 ((schedule 20).drop 4) 0 262140 2 = true := by decide +kernel

private theorem cert20 : finiteCheck 20 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_20_1111 finite_20_1110) (search_step (by decide) (by decide) finite_20_1101 finite_20_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_20_1011 finite_20_1010) (search_step (by decide) (by decide) finite_20_1001 finite_20_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_20_0111 finite_20_0110) (search_step (by decide) (by decide) finite_20_0101 finite_20_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_20_0011 finite_20_0010) (search_step (by decide) (by decide) finite_20_0001 finite_20_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_1111 :
    search 21 ((schedule 21).drop 4) 1572867 2097151 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_1110 :
    search 21 ((schedule 21).drop 4) 1048579 1572863 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_1101 :
    search 21 ((schedule 21).drop 4) 1572865 2097149 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_1100 :
    search 21 ((schedule 21).drop 4) 1048577 1572861 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_1011 :
    search 21 ((schedule 21).drop 4) 524291 1048575 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_1010 :
    search 21 ((schedule 21).drop 4) 3 524287 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_1001 :
    search 21 ((schedule 21).drop 4) 524289 1048573 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_1000 :
    search 21 ((schedule 21).drop 4) 1 524285 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_0111 :
    search 21 ((schedule 21).drop 4) 1572866 2097150 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_0110 :
    search 21 ((schedule 21).drop 4) 1048578 1572862 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_0101 :
    search 21 ((schedule 21).drop 4) 1572864 2097148 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_0100 :
    search 21 ((schedule 21).drop 4) 1048576 1572860 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_0011 :
    search 21 ((schedule 21).drop 4) 524290 1048574 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_0010 :
    search 21 ((schedule 21).drop 4) 2 524286 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_0001 :
    search 21 ((schedule 21).drop 4) 524288 1048572 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_21_0000 :
    search 21 ((schedule 21).drop 4) 0 524284 2 = true := by decide +kernel

private theorem cert21 : finiteCheck 21 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_21_1111 finite_21_1110) (search_step (by decide) (by decide) finite_21_1101 finite_21_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_21_1011 finite_21_1010) (search_step (by decide) (by decide) finite_21_1001 finite_21_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_21_0111 finite_21_0110) (search_step (by decide) (by decide) finite_21_0101 finite_21_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_21_0011 finite_21_0010) (search_step (by decide) (by decide) finite_21_0001 finite_21_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_1111 :
    search 22 ((schedule 22).drop 4) 3145731 4194303 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_1110 :
    search 22 ((schedule 22).drop 4) 2097155 3145727 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_1101 :
    search 22 ((schedule 22).drop 4) 3145729 4194301 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_1100 :
    search 22 ((schedule 22).drop 4) 2097153 3145725 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_1011 :
    search 22 ((schedule 22).drop 4) 1048579 2097151 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_1010 :
    search 22 ((schedule 22).drop 4) 3 1048575 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_1001 :
    search 22 ((schedule 22).drop 4) 1048577 2097149 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_1000 :
    search 22 ((schedule 22).drop 4) 1 1048573 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_0111 :
    search 22 ((schedule 22).drop 4) 3145730 4194302 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_0110 :
    search 22 ((schedule 22).drop 4) 2097154 3145726 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_0101 :
    search 22 ((schedule 22).drop 4) 3145728 4194300 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_0100 :
    search 22 ((schedule 22).drop 4) 2097152 3145724 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_0011 :
    search 22 ((schedule 22).drop 4) 1048578 2097150 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_0010 :
    search 22 ((schedule 22).drop 4) 2 1048574 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_0001 :
    search 22 ((schedule 22).drop 4) 1048576 2097148 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_22_0000 :
    search 22 ((schedule 22).drop 4) 0 1048572 2 = true := by decide +kernel

private theorem cert22 : finiteCheck 22 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_22_1111 finite_22_1110) (search_step (by decide) (by decide) finite_22_1101 finite_22_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_22_1011 finite_22_1010) (search_step (by decide) (by decide) finite_22_1001 finite_22_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_22_0111 finite_22_0110) (search_step (by decide) (by decide) finite_22_0101 finite_22_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_22_0011 finite_22_0010) (search_step (by decide) (by decide) finite_22_0001 finite_22_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_1111 :
    search 23 ((schedule 23).drop 4) 6291459 8388607 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_1110 :
    search 23 ((schedule 23).drop 4) 4194307 6291455 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_1101 :
    search 23 ((schedule 23).drop 4) 6291457 8388605 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_1100 :
    search 23 ((schedule 23).drop 4) 4194305 6291453 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_1011 :
    search 23 ((schedule 23).drop 4) 2097155 4194303 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_1010 :
    search 23 ((schedule 23).drop 4) 3 2097151 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_1001 :
    search 23 ((schedule 23).drop 4) 2097153 4194301 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_1000 :
    search 23 ((schedule 23).drop 4) 1 2097149 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_0111 :
    search 23 ((schedule 23).drop 4) 6291458 8388606 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_0110 :
    search 23 ((schedule 23).drop 4) 4194306 6291454 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_0101 :
    search 23 ((schedule 23).drop 4) 6291456 8388604 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_0100 :
    search 23 ((schedule 23).drop 4) 4194304 6291452 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_0011 :
    search 23 ((schedule 23).drop 4) 2097154 4194302 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_0010 :
    search 23 ((schedule 23).drop 4) 2 2097150 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_0001 :
    search 23 ((schedule 23).drop 4) 2097152 4194300 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_23_0000 :
    search 23 ((schedule 23).drop 4) 0 2097148 2 = true := by decide +kernel

private theorem cert23 : finiteCheck 23 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_23_1111 finite_23_1110) (search_step (by decide) (by decide) finite_23_1101 finite_23_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_23_1011 finite_23_1010) (search_step (by decide) (by decide) finite_23_1001 finite_23_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_23_0111 finite_23_0110) (search_step (by decide) (by decide) finite_23_0101 finite_23_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_23_0011 finite_23_0010) (search_step (by decide) (by decide) finite_23_0001 finite_23_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_1111 :
    search 24 ((schedule 24).drop 4) 12582915 16777215 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_1110 :
    search 24 ((schedule 24).drop 4) 8388611 12582911 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_1101 :
    search 24 ((schedule 24).drop 4) 12582913 16777213 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_1100 :
    search 24 ((schedule 24).drop 4) 8388609 12582909 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_1011 :
    search 24 ((schedule 24).drop 4) 4194307 8388607 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_1010 :
    search 24 ((schedule 24).drop 4) 3 4194303 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_1001 :
    search 24 ((schedule 24).drop 4) 4194305 8388605 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_1000 :
    search 24 ((schedule 24).drop 4) 1 4194301 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_0111 :
    search 24 ((schedule 24).drop 4) 12582914 16777214 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_0110 :
    search 24 ((schedule 24).drop 4) 8388610 12582910 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_0101 :
    search 24 ((schedule 24).drop 4) 12582912 16777212 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_0100 :
    search 24 ((schedule 24).drop 4) 8388608 12582908 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_0011 :
    search 24 ((schedule 24).drop 4) 4194306 8388606 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_0010 :
    search 24 ((schedule 24).drop 4) 2 4194302 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_0001 :
    search 24 ((schedule 24).drop 4) 4194304 8388604 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_24_0000 :
    search 24 ((schedule 24).drop 4) 0 4194300 2 = true := by decide +kernel

private theorem cert24 : finiteCheck 24 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_24_1111 finite_24_1110) (search_step (by decide) (by decide) finite_24_1101 finite_24_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_24_1011 finite_24_1010) (search_step (by decide) (by decide) finite_24_1001 finite_24_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_24_0111 finite_24_0110) (search_step (by decide) (by decide) finite_24_0101 finite_24_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_24_0011 finite_24_0010) (search_step (by decide) (by decide) finite_24_0001 finite_24_0000)))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_1111 :
    search 25 ((schedule 25).drop 4) 25165827 33554431 6 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_1110 :
    search 25 ((schedule 25).drop 4) 16777219 25165823 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_1101 :
    search 25 ((schedule 25).drop 4) 25165825 33554429 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_1100 :
    search 25 ((schedule 25).drop 4) 16777217 25165821 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_1011 :
    search 25 ((schedule 25).drop 4) 8388611 16777215 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_1010 :
    search 25 ((schedule 25).drop 4) 3 8388607 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_1001 :
    search 25 ((schedule 25).drop 4) 8388609 16777213 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_1000 :
    search 25 ((schedule 25).drop 4) 1 8388605 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_0111 :
    search 25 ((schedule 25).drop 4) 25165826 33554430 5 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_0110 :
    search 25 ((schedule 25).drop 4) 16777218 25165822 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_0101 :
    search 25 ((schedule 25).drop 4) 25165824 33554428 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_0100 :
    search 25 ((schedule 25).drop 4) 16777216 25165820 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_0011 :
    search 25 ((schedule 25).drop 4) 8388610 16777214 4 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_0010 :
    search 25 ((schedule 25).drop 4) 2 8388606 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_0001 :
    search 25 ((schedule 25).drop 4) 8388608 16777212 3 = true := by decide +kernel

set_option maxRecDepth 5000 in
set_option maxHeartbeats 0 in
private theorem finite_25_0000 :
    search 25 ((schedule 25).drop 4) 0 8388604 2 = true := by decide +kernel

private theorem cert25 : finiteCheck 25 = true :=
  search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_25_1111 finite_25_1110) (search_step (by decide) (by decide) finite_25_1101 finite_25_1100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_25_1011 finite_25_1010) (search_step (by decide) (by decide) finite_25_1001 finite_25_1000))) (search_step (by decide) (by decide) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_25_0111 finite_25_0110) (search_step (by decide) (by decide) finite_25_0101 finite_25_0100)) (search_step (by decide) (by decide) (search_step (by decide) (by decide) finite_25_0011 finite_25_0010) (search_step (by decide) (by decide) finite_25_0001 finite_25_0000)))


private theorem bounded_width {N : ℤ} {A : Finset ℤ} (h₁ : 15 ≤ N) (h₂ : N ≤ 24)
    (hA : A ⊆ Icc 0 N) (budget : (holes N A).card ≤ 6) :
    2 * (posMissing N A).card ≤ (sumMissing N A).card := by
  let n := (N + 1).toNat
  have hn : (n : ℤ) = N+1 := Int.toNat_of_nonneg (by omega)
  have hfull : encoded n (2^n-1) = Icc 0 N := by
    ext x
    simp only [mem_encoded, Nat.testBit_two_pow_sub_one, decide_eq_true_eq, mem_Icc]
    omega
  have hnil : encoded n 0 ⊆ A := by
    intro x hx
    have hfalse := (mem_encoded.mp hx).2.2
    simp at hfalse
  have hcheck : finiteCheck n = true := by
    have h₀ : 16 ≤ n := by omega
    have h₁ : n ≤ 25 := by omega
    rcases (show n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 by omega) with e | e | e | e | e | e | e | e | e | e
    · rw [e]; exact cert16
    · rw [e]; exact cert17
    · rw [e]; exact cert18
    · rw [e]; exact cert19
    · rw [e]; exact cert20
    · rw [e]; exact cert21
    · rw [e]; exact cert22
    · rw [e]; exact cert23
    · rw [e]; exact cert24
    · rw [e]; exact cert25
  exact search_sound hn (by omega) hA budget (schedule n) hnil (hfull ▸ hA)
    (by rw [hfull]; exact budget) hcheck

private theorem upper_bound {N : ℤ} {A : Finset ℤ} (hN : 15 ≤ N)
    (hA : A ⊆ Icc 0 N) (h : (holes N A).card ≤ 6) :
    2 * (posMissing N A).card ≤ (sumMissing N A).card := by
  by_cases hsmall : N ≤ 24
  · exact bounded_width hN hsmall hA h
  · obtain ⟨hs, hd⟩ := compress_counts (by omega) hA h
    rw [hs, hd]
    exact bounded_width (by decide) le_rfl sdiff_subset ((compressed_holes N A).trans h)

private def witness16 : Finset ℤ := {0,1,3,7,8,11,13,14,15}

set_option maxRecDepth 5000 in
private theorem witness16_valid :
    witness16 ⊆ Icc 0 15 ∧ witness16.card = 9 ∧
    (witness16 - witness16).card < (witness16 + witness16).card := by decide

private def witness17 : Finset ℤ := {0,2,3,7,8,9,11,14,15,16}

set_option maxRecDepth 5000 in
private theorem witness17_valid :
    witness17 ⊆ Icc 0 16 ∧ witness17.card = 10 ∧
    (witness17 - witness17).card < (witness17 + witness17).card := by decide

theorem exactMaximum (n : ℕ) (hn : 15 < n) : OMA.S_oeis_a305503.maxMSTD n = n - 7 := by
  let N : ℤ := (n : ℤ)-1
  have hN : 15 ≤ N := by dsimp [N]; omega
  have hI : Ico (0 : ℤ) (n : ℤ) = Icc 0 N := by
    ext x
    simp only [mem_Ico, mem_Icc]
    dsimp [N]
    omega
  unfold OMA.S_oeis_a305503.maxMSTD
  rw [hI]
  let S : Set ℕ := {k | ∃ A : Finset ℤ, A ⊆ Icc 0 N ∧ A.card = k ∧
    (A - A).card < (A + A).card}
  change sSup S = n - 7
  have attain : n - 7 ∈ S := by
    have change_card : (N - 6).toNat = n - 7 := by dsimp [N]; omega
    rcases (show n = 16 ∨ n = 17 ∨ 18 ≤ n by omega) with rfl | rfl | h18
    · exact ⟨witness16, witness16_valid.1, witness16_valid.2.1, witness16_valid.2.2⟩
    · exact ⟨witness17, witness17_valid.1, witness17_valid.2.1, witness17_valid.2.2⟩
    · have h₁ : 17 ≤ N := by dsimp [N]; omega
      exact ⟨witness N, sdiff_subset, (witness_card (by omega)).trans change_card, witness_good h₁⟩
  have bound : ∀ k ∈ S, k ≤ n - 7 := by
    intro k hk
    obtain ⟨A, hA, hcard, hgood⟩ := hk
    by_contra! hlarge
    have ha : A.Nonempty := card_pos.mp (by omega)
    have hl := holes_card hA
    have hn' : (N + 1).toNat = n := by dsimp [N]; omega
    rw [hn', hcard] at hl
    exact (not_lt_of_ge (upper_bound hN hA (by omega))) ((more_sums_iff hA ha).mp hgood)
  exact le_antisymm (csSup_le ⟨_, attain⟩ bound) (le_csSup ⟨_, bound⟩ attain)

end OMA.A305503

theorem OMA.solution : type_of% @OMA.S_oeis_a305503.main :=
  OMA.A305503.exactMaximum
