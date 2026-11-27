import OMAReductions.R_Erdos145_erdos_145_variants_lt_eleven_thirds_R1_H2_R1
import Mathlib

/-! Each gap contributes the first half of its possible starting positions.
Bertrand's theorem keeps even the last such interval in the counting window. -/

open Erdos145 Finset

private lemma next_le_of_squarefree {n z : ℕ} (h : s n < z) (hs : Squarefree z) :
    s (n+1) ≤ z := by
  obtain ⟨i,hi⟩ := (Nat.subset_range_nth (p := Squarefree)) (show z ∈ Set.ofPred Squarefree from hs)
  change s i = z at hi
  have mono : StrictMono s := Nat.nth_strictMono Nat.squarefree_infinite
  rw [← hi] at h ⊢
  exact mono.monotone (show n+1 ≤ i from mono.lt_iff_lt.mp h)

private lemma next_le_double (n : ℕ) : s (n+1) ≤ 2*s n := by
  have h : Squarefree (s n) := Nat.nth_mem_of_infinite Nat.squarefree_infinite n
  obtain ⟨p,hp,hn,hu⟩ := Nat.exists_prime_lt_and_le_two_mul (s n) h.ne_zero
  exact (next_le_of_squarefree hn hp.squarefree).trans hu

theorem OMA.solution : OMA.R_Erdos145_erdos_145_variants_lt_eleven_thirds_R1_H2_R1.H1 := by
  classical
  intro x hx k
  let W := 2^k
  let m := (W+1)/2
  let G := (A x).filter fun n => Nat.log 2 (s (n+1)-s n) = k
  let B := (range (2*⌊x⌋₊+5)).filter fun v => ∀ j ∈ Ioo 0 (W/2), ¬ Squarefree (v+j)
  change W*G.card ≤ 4*B.card
  have mono : StrictMono s := Nat.nth_strictMono Nat.squarefree_infinite
  have gap {n} (hn : n ∈ G) : W ≤ s (n+1)-s n := by
    have he := (mem_filter.mp hn).2
    have hp := Nat.sub_pos_of_lt (mono (Nat.lt_succ_self n))
    simpa only [he] using Nat.pow_log_le_self 2 hp.ne'
  have bound {n} (hn : n ∈ G) : s n ≤ ⌊x⌋₊ :=
    (mem_Icc.mp (mem_preimage.mp (mem_filter.mp hn).1)).2
  have endpos {n i} (hn : n ∈ G) (hi : i < m) : s n + i < s (n+1) := by
    have := gap hn
    have : 0 < W := pow_pos (by decide) _
    dsimp [m] at hi
    omega
  let f (u : ℕ × ℕ) := s u.1 + u.2
  have maps : Set.MapsTo f (G ×ˢ range m : Finset _) B := by
    rintro ⟨n,i⟩ hu
    obtain ⟨hn,hi⟩ := mem_product.mp hu
    change n ∈ G at hn
    change i ∈ range m at hi
    have hi' := mem_range.mp hi
    have e := endpos hn hi'
    have ub := bound hn
    have dub := next_le_double n
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by dsimp [f]; omega), ?_⟩
    intro j hj sq
    obtain ⟨hj1,hj2⟩ := mem_Ioo.mp hj
    change Squarefree (s n+i+j) at sq
    have := next_le_of_squarefree (n:=n) (z:=s n+i+j) (by omega) sq
    have := gap hn
    change i < (W+1)/2 at hi'
    omega
  have inj : Set.InjOn f (G ×ˢ range m : Finset _) := by
    rintro ⟨n,i⟩ hn ⟨t,j⟩ ht he
    obtain ⟨hn,hi⟩ := mem_product.mp hn
    obtain ⟨ht,hj⟩ := mem_product.mp ht
    change n ∈ G at hn
    change t ∈ G at ht
    change i ∈ range m at hi
    change j ∈ range m at hj
    dsimp [f] at he
    have ei := endpos hn (mem_range.mp hi)
    have ej := endpos ht (mem_range.mp hj)
    have nt : n = t := by
      rcases lt_trichotomy n t with h|h|h
      · have := mono.monotone (show n+1 ≤ t from h)
        omega
      · exact h
      · have := mono.monotone (show t+1 ≤ n from h)
        omega
    subst t
    exact Prod.ext rfl (by omega)
  have hc := card_le_card_of_injOn f maps inj
  simp only [card_product, card_range] at hc
  have hw : W ≤ 4*m := by dsimp [m]; omega
  calc
    W*G.card ≤ (4*m)*G.card := Nat.mul_le_mul_right _ hw
    _ = 4*(G.card*m) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hc
