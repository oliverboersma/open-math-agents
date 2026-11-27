import FormalConjectures.OEIS.«331631»

/-!
The tripling construction enumerates every positive integer exactly once.
A power of three is one modulo the decimal place value just above the seed,
so some term ends in the seed. To prevent repetitions, each finite history
is kept closed under taking the predecessor of a multiple of three.
-/

namespace OMA.Tripling

open OeisA331631

private theorem exists_stop (s : ℕ) : ∃ e, StopsAt s e := by
  classical
  let d := 10 ^ (Nat.digits 10 s).length
  have hc : Nat.Coprime 3 d :=
    Nat.Coprime.pow_right _ (by decide : Nat.Coprime 3 10)
  have hm : s ≡ s * 3 ^ d.totient [MOD d] := by
    simpa using (Nat.ModEq.pow_totient hc).symm.mul_left s
  have hle : s ≤ s * 3 ^ d.totient := Nat.le_mul_of_pos_right _ (by positivity)
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hm
  have hex : ∃ e, 0 < e ∧ ContainsSeed s (s * 3 ^ e) := by
    refine ⟨d.totient, Nat.totient_pos.mpr (by dsimp [d]; positivity), ?_⟩
    unfold ContainsSeed
    rw [hu, ← Nat.digits_append_digits (by decide : 0 < 10)]
    exact (List.prefix_append _ _).isInfix
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro j hj hlt hcontains
  exact (Nat.find_min hex hlt) ⟨hj, hcontains⟩

private noncomputable def stop (s : ℕ) := (exists_stop s).choose

private theorem stop_spec (s : ℕ) : StopsAt s (stop s) := (exists_stop s).choose_spec

private theorem missing_exists (l : List ℕ) : ∃ s, 0 < s ∧ s ∉ l := by
  refine ⟨l.sum + 1, by omega, fun h => ?_⟩
  have := List.le_sum_of_mem h
  omega

private def seed (l : List ℕ) := Nat.find (missing_exists l)

private theorem seed_spec (l : List ℕ) : 0 < seed l ∧ seed l ∉ l :=
  Nat.find_spec (missing_exists l)

private theorem seed_le (l : List ℕ) {k : ℕ} (hk : 0 < k) (h : k ∉ l) :
    seed l ≤ k := Nat.find_min' (missing_exists l) ⟨hk, h⟩

private theorem mem_of_lt_seed (l : List ℕ) {k : ℕ} (hk : 0 < k) (hlt : k < seed l) :
    k ∈ l := by
  by_contra h
  exact hlt.not_ge (seed_le l hk h)

private noncomputable def history : ℕ → List ℕ
  | 0 => []
  | b + 1 => history b ++ blockValues (seed (history b)) (stop (seed (history b)))

private def DownClosed (l : List ℕ) := ∀ k, k * 3 ∈ l → k ∈ l

private theorem mem_block {s e v : ℕ} :
    v ∈ blockValues s e ↔ ∃ j ≤ e, s * 3 ^ j = v := by
  simp [blockValues]

private lemma peel {l : List ℕ} (hc : DownClosed l) (s j : ℕ)
    (h : s * 3 ^ j ∈ l) : s ∈ l := by
  induction j with
  | zero => simpa using h
  | succ j ih => exact ih (hc _ (by simpa [pow_succ, Nat.mul_assoc] using h))

private theorem append_closed {l : List ℕ} (hc : DownClosed l) (e : ℕ) :
    DownClosed (l ++ blockValues (seed l) e) := by
  intro k hk
  rcases List.mem_append.mp hk with h | h
  · exact List.mem_append_left _ (hc _ h)
  obtain ⟨j, hj, heq⟩ := mem_block.mp h
  cases j with
  | zero =>
    simp only [pow_zero, mul_one] at heq
    have hpos := (seed_spec l).1
    exact List.mem_append_left _ (mem_of_lt_seed l (by omega) (by omega))
  | succ j =>
    rw [pow_succ, ← Nat.mul_assoc] at heq
    exact List.mem_append_right _ (mem_block.mpr ⟨j, by omega, by omega⟩)

private theorem history_good (b : ℕ) : DownClosed (history b) ∧ (history b).Nodup := by
  induction b with
  | zero => exact ⟨by simp [history, DownClosed], by simp [history]⟩
  | succ b ih =>
    let l := history b
    let s := seed l
    let e := stop s
    change DownClosed (l ++ blockValues s e) ∧ (l ++ blockValues s e).Nodup
    refine ⟨append_closed ih.1 e, List.nodup_append.mpr ⟨ih.2, ?_, ?_⟩⟩
    · unfold blockValues
      apply List.Nodup.map _ List.nodup_range
      intro i j h
      exact Nat.pow_right_injective (by decide : 2 ≤ 3)
        (Nat.eq_of_mul_eq_mul_left (seed_spec l).1 h)
    · rintro a ha _ hb rfl
      obtain ⟨j, _, h⟩ := mem_block.mp hb
      exact (seed_spec l).2 (peel ih.1 s j (h ▸ ha))

private theorem hist_prefix {b c : ℕ} (h : b ≤ c) : history b <+: history c := by
  induction h with
  | refl => rfl
  | step h ih => exact ih.trans (List.prefix_append _ _)

private theorem len_ge (b : ℕ) : b ≤ (history b).length := by
  induction b with
  | zero => omega
  | succ b ih =>
    simp only [history, List.length_append, block_values_length]
    omega

private noncomputable def term (n : ℕ) := (history (n+1))[n]'(by have := len_ge (n+1); omega)

private theorem agrees (b i : ℕ) (hi : i < (history b).length) :
    term i = (history b)[i] := by
  unfold term
  rcases le_total (i+1) b with h | h
  · exact (hist_prefix h).getElem _
  · exact ((hist_prefix h).getElem _).symm

private theorem at_offset (b j : ℕ) (hj : j ≤ stop (seed (history b))) :
    term ((history b).length + j) = seed (history b) * 3 ^ j := by
  have hi : (history b).length + j < (history (b+1)).length := by
    simp only [history, List.length_append, block_values_length]; omega
  rw [agrees (b+1) _ hi]
  simp [history, List.getElem_append_right, blockValues]

private theorem seed_succ (b : ℕ) : seed (history b) < seed (history (b+1)) := by
  have hn := seed_spec (history (b+1))
  have hs := seed_spec (history b)
  by_contra! h
  rcases h.lt_or_eq with h | h
  · exact hn.2 (List.mem_append_left _ (mem_of_lt_seed _ hn.1 h))
  · apply hn.2
    rw [h]
    exact List.mem_append_right _ (mem_block.mpr ⟨0, Nat.zero_le _, by simp⟩)

end OMA.Tripling

open OMA.Tripling OeisA331631 in
theorem OMA.solution : type_of% @OeisA331631.conjecture := by
  refine ⟨term, ⟨fun b => (history b).length, fun b => stop (seed (history b)), rfl, ?_⟩, ?_, ?_⟩
  · intro b
    dsimp only
    have first : term (history b).length = seed (history b) := by
      simpa using at_offset b 0 (Nat.zero_le _)
    rw [first]
    refine ⟨⟨⟨(seed_spec _).1, ?_⟩, ?_⟩, stop_spec _, at_offset b, ?_⟩
    · intro i hi heq
      exact (seed_spec _).2 (heq ▸ (agrees b i hi).symm ▸ List.getElem_mem _)
    · intro k hk
      apply seed_le _ hk.1
      intro hmem
      obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.mp hmem
      exact hk.2 i hi ((agrees b i hi).trans h)
    · simp [history, block_values_length, Nat.add_assoc]
  · intro i j h
    let b := max i j + 1
    have hi : i < (history b).length := by have := len_ge b; dsimp [b] at *; omega
    have hj : j < (history b).length := by have := len_ge b; dsimp [b] at *; omega
    apply (history_good b).2.getElem_inj_iff.mp
    exact (agrees b i hi).symm.trans (h.trans (agrees b j hj))
  · intro k hk
    have hg : ∀ b, b < seed (history b) := by
      intro b
      induction b with
      | zero => exact (seed_spec _).1
      | succ b ih => have := seed_succ b; omega
    obtain ⟨i, hi, h⟩ := List.mem_iff_getElem.mp (mem_of_lt_seed (history k) hk (hg k))
    exact ⟨i, (agrees k i hi).trans h⟩
