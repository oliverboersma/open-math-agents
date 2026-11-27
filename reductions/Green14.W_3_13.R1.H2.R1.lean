import OMAReductions.R_Green14_W_3_13_R1

/-!
# The two medium central gaps on 160 positions

Work on the 158 interior positions numbered 1 through 158. In the six-blue
case this shorter interval alone suffices. In the four-blue case some
interior colorings extend to the left and some extend to the right.
An extension with red at an endpoint fails if two interior reds complete
a three-term progression there. An extension with blue fails if twelve
interior blues complete a thirteen-term progression there. No progression
of either length uses both endpoints, since their distance is odd.

The natural-number color functions below are only read at interior positions.
Each red endpoint is ruled out separately. For two blue endpoints a
single twelve-blue run suffices, at either end.
Credit: @ZedingZhang. The central-gap normalization is due to @NickLeko.
-/

namespace OMA.R_Green14_W_3_13_R1_H2_R1

private lemma blocked_extension (c : ℕ → Bool) (l r : Bool)
    (hl : c 0 = l) (hr : c 159 = r)
    (h : (∃ d : ℕ, 0 < d ∧ (if l then 2 else 12) * d < 159 ∧
            ∀ t : Fin 13, 0 < t.val → t.val ≤ (if l then 2 else 12) → c (t.val * d) = l) ∨
         (∃ a d : ℕ, 0 < a ∧ 0 < d ∧ a + (if r then 2 else 12) * d = 159 ∧
            ∀ t : Fin 13, t.val < (if r then 2 else 12) → c (a + t.val * d) = r)) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 12) * d < 160 ∧
      ∀ t : Fin 13, t.val ≤ (if b then 2 else 12) → c (a + t.val * d) = b := by
  rcases h with ⟨d, hd, bound, run⟩ | ⟨a, d, _, hd, endAt, run⟩
  · refine ⟨l, 0, d, hd, by simpa using (Nat.lt_trans bound (by decide : 159 < 160)), ?_⟩
    intro t ht
    by_cases hz : t.val = 0
    · simpa [hz] using hl
    · simpa using run t (by omega) ht
  · refine ⟨r, a, d, hd, by omega, ?_⟩
    intro t ht
    by_cases he : t.val = (if r then 2 else 12)
    · simpa only [he, endAt] using hr
    · exact run t (by omega)

private lemma finite_progression (r : Fin 160 → Bool)
    (h : ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 12) * d < 160 ∧
      ∀ t : Fin 13, t.val ≤ (if b then 2 else 12) → r (Fin.ofNat 160 (a + t.val * d)) = b) :
    ∃ (b : Bool) (a d : Fin 160), 0 < d.val ∧ a.val + (if b then 2 else 12) * d.val < 160 ∧
      ∀ t : Fin 13, t.val ≤ (if b then 2 else 12) → r (Fin.ofNat 160 (a.val + t.val * d.val)) = b := by
  obtain ⟨b, a, d, hd, bound, run⟩ := h
  have ha : a < 160 := by omega
  have hd' : d < 160 := by cases b <;> simp at bound <;> omega
  exact ⟨b, ⟨a, ha⟩, ⟨d, hd'⟩, hd, bound, run⟩

private lemma red_triple (c : ℕ → Bool) (a d : ℕ) (hd : 0 < d)
    (bound : a + 2*d < 160) (ha : c a = true)
    (hm : c (a+d) = true) (he : c (a+2*d) = true) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 12) * d < 160 ∧
      ∀ t : Fin 13, t.val ≤ (if b then 2 else 12) → c (a + t.val * d) = b := by
  refine ⟨true, a, d, hd, bound, ?_⟩
  intro t ht
  change t.val ≤ 2 at ht
  have cases' : t.val = 0 ∨ t.val = 1 ∨ t.val = 2 := by omega
  rcases cases' with h | h | h
  · simpa only [h, zero_mul, Nat.add_zero] using ha
  · simpa only [h, one_mul] using hm
  · simpa only [h] using he

/-- A red 76 followed by six blues forces a progression inside 1 through 158. -/
def H1 : Prop :=
  ∀ c : ℕ → Bool, c 76 = true →
    (∀ i, 76 < i → i < 83 → c i = false) →
    ∃ (b : Bool) (a d : ℕ), 0 < a ∧ 0 < d ∧ a + (if b then 2 else 12) * d < 159 ∧
      ∀ t : Fin 13, t.val ≤ (if b then 2 else 12) → c (a + t.val * d) = b

/-- Two interior reds obstruct a red at position zero. -/
def H2 : Prop :=
  ∀ c : ℕ → Bool, c 77 = true →
    (∀ i, 77 < i → i < 82 → c i = false) →
    (∀ (b : Bool) (a d : ℕ), 0 < a → 0 < d → a + (if b then 2 else 12) * d < 159 →
      ∃ t : Fin 13, t.val ≤ (if b then 2 else 12) ∧ c (a + t.val * d) ≠ b) →
    ∃ d : ℕ, 0 < d ∧ 2*d < 159 ∧ c d = true ∧ c (2*d) = true

/-- Two interior reds obstruct a red at position 159. -/
def H3 : Prop :=
  ∀ c : ℕ → Bool, c 77 = true →
    (∀ i, 77 < i → i < 82 → c i = false) →
    (∀ (b : Bool) (a d : ℕ), 0 < a → 0 < d → a + (if b then 2 else 12) * d < 159 →
      ∃ t : Fin 13, t.val ≤ (if b then 2 else 12) ∧ c (a + t.val * d) ≠ b) →
    ∃ a d : ℕ, 0 < a ∧ 0 < d ∧ a + 2*d = 159 ∧ c a = true ∧ c (a+d) = true

/-- One of the two endpoints completes twelve interior blues to a thirteen-term progression. -/
def H4 : Prop :=
  ∀ c : ℕ → Bool, c 77 = true →
    (∀ i, 77 < i → i < 82 → c i = false) →
    (∀ (b : Bool) (a d : ℕ), 0 < a → 0 < d → a + (if b then 2 else 12) * d < 159 →
      ∃ t : Fin 13, t.val ≤ (if b then 2 else 12) ∧ c (a + t.val * d) ≠ b) →
    (∃ d : ℕ, 0 < d ∧ 12*d < 159 ∧
      ∀ t : Fin 13, 0 < t.val → t.val ≤ 12 → c (t.val*d) = false) ∨
    (∃ a d : ℕ, 0 < a ∧ 0 < d ∧ a + 12*d = 159 ∧
      ∀ t : Fin 13, t.val < 12 → c (a + t.val*d) = false)

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_13_R1.H2 := by
  intro six leftRed rightRed bothBlue r j low high anchor gap
  let c (n : ℕ) := r (Fin.ofNat 160 n)
  have red : c (79 - j.val) = true := anchor
  have blue (i : ℕ) (hleft : 79 - j.val < i) (hright : i < 80 + j.val) : c i = false := by
    have hi : i < 160 := by omega
    apply gap (Fin.ofNat 160 i)
    · simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hi] using hleft
    · simpa only [Fin.val_ofNat, Nat.mod_eq_of_lt hi] using hright
  apply finite_progression r
  change ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 12) * d < 160 ∧
    ∀ t : Fin 13, t.val ≤ (if b then 2 else 12) → c (a + t.val * d) = b
  by_cases hj : j.val = 3
  · have hr : c 76 = true := by simpa [hj] using red
    have hb (i : ℕ) (hl : 76 < i) (hu : i < 83) := blue i (by omega) (by omega)
    obtain ⟨b, a, d, _, hd, bound, hm⟩ := six c hr hb
    exact ⟨b, a, d, hd, by omega, hm⟩
  · have hj' : j.val = 2 := by omega
    have hr : c 77 = true := by simpa [hj'] using red
    have hb (i : ℕ) (hl : 77 < i) (hu : i < 82) := blue i (by omega) (by omega)
    by_contra no
    have inside (b : Bool) (a d : ℕ) (_ : 0 < a) (hd : 0 < d)
        (bound : a + (if b then 2 else 12) * d < 159) :
        ∃ t : Fin 13, t.val ≤ (if b then 2 else 12) ∧ c (a + t.val * d) ≠ b := by
      by_contra none
      apply no
      refine ⟨b, a, d, hd, by omega, ?_⟩
      intro t ht
      by_contra hne
      exact none ⟨t, ht, hne⟩
    by_cases west : c 0 = true
    · obtain ⟨d, hd, bound, hmid, hend⟩ := leftRed c hr hb inside
      apply no
      exact red_triple c 0 d hd (by simpa using (Nat.lt_trans bound (by decide : 159 < 160)))
        west (by simpa using hmid) (by simpa using hend)
    by_cases east : c 159 = true
    · obtain ⟨a, d, _, hd, hend, hfirst, hmid⟩ := rightRed c hr hb inside
      exact no (red_triple c a d hd (by omega) hfirst hmid (by simpa only [hend] using east))
    have west' : c 0 = false := Bool.eq_false_iff.mpr west
    have east' : c 159 = false := Bool.eq_false_iff.mpr east
    exact no (blocked_extension c false false west' east' (bothBlue c hr hb inside))

end OMA.R_Green14_W_3_13_R1_H2_R1
