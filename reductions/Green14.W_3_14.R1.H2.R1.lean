import OMAReductions.R_Green14_W_3_14_R1

/-!
Shifting by `3-j` aligns the two center gaps in a common 185-position window.
The first four possible red positions require new certificates. A second shift
by three sends the remaining six placements to the 182-position window used
for the outer center gaps.
-/

namespace OMA.R_Green14_W_3_14_R1_H2_R1

def H1 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 94 = true →
    (∀ q : Nat, 89 < q → q < 94 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ c : Nat → Bool, c 89 = true → c 95 = true →
    (∀ q : Nat, 89 < q → q < 95 → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), 96 ≤ p → p ≤ 97 →
    c 89 = true → c p = true → (∀ q : Nat, 89 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H4 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), 95 ≤ p → p ≤ 100 →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem window (h1 : H1) (h2 : H2) (h3 : H3) (h4 : H4)
    (c : Nat → Bool) (anchor : c 89 = true)
    (gap : ∀ q : Nat, 89 < q → q ≤ 93 → c q = false) :
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 185 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b := by
  classical
  by_cases allBlue : ∀ q : Nat, 90 ≤ q → q ≤ 103 → c q = false
  · refine ⟨false, 90, 1, by decide, by decide, ?_⟩
    intro t ht
    simpa using allBlue (90+t.val) (by omega) (by omega)
  · push Not at allBlue
    obtain ⟨z, lo, hi, hz⟩ := allBlue
    have existsRed : ∃ q : Nat, 90 ≤ q ∧ q ≤ 103 ∧ c q = true :=
      ⟨z, lo, hi, Bool.ne_false_iff.mp hz⟩
    let p := Nat.find existsRed
    obtain ⟨lower, upper, red⟩ : 90 ≤ p ∧ p ≤ 103 ∧ c p = true := Nat.find_spec existsRed
    have before (q : Nat) (lo : 89 < q) (hi : q < p) : c q = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact Nat.find_min existsRed hi ⟨by omega, by omega, h⟩
    have first : 94 ≤ p := by
      by_contra! early
      exact Bool.false_ne_true ((gap p (by omega) (by omega)).symm.trans red)
    by_cases h94 : p = 94
    · exact h1 c anchor (by rw [← h94]; exact red) (by rw [← h94]; exact before)
    by_cases h95 : p = 95
    · exact h2 c anchor (by rw [← h95]; exact red) (by rw [← h95]; exact before)
    by_cases early : p ≤ 97
    · exact h3 c p (by omega) early anchor red before
    let shifted (q : Nat) := c (3+q)
    have shiftedRed : shifted (p-3) = true := by
      have hp : 3+(p-3) = p := by omega
      simpa only [shifted, hp] using red
    have shiftedGap (q : Nat) (lo : 86 < q) (hi : q < p-3) : shifted q = false :=
      before (3+q) (by omega) (by omega)
    obtain ⟨b, a, d, step, bound, run⟩ :=
      h4 shifted (p-3) (by omega) (by omega) anchor shiftedRed shiftedGap
    refine ⟨b, 3+a, d, step, by omega, ?_⟩
    intro t ht
    simpa only [shifted, Nat.add_assoc] using run t ht

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_14_R1.H2 := by
  intro h1 h2 h3 h4 r j lo hi anchor gap
  let offset := 3-j.val
  have offsetBound : offset ≤ 1 := by dsimp [offset]; omega
  have anchorIndex : offset+89 = 92-j.val := by dsimp [offset]; omega
  let c (q : Nat) : Bool := r (Fin.ofNat 186 (offset+q))
  have start : c 89 = true := by simpa only [c, anchorIndex] using anchor
  have fourBlue (q : Nat) (hlo : 89 < q) (hhi : q ≤ 93) : c q = false := by
    have inRange : offset+q < 186 := by omega
    have index : (Fin.ofNat 186 (offset+q)).val = offset+q := Nat.mod_eq_of_lt inRange
    apply gap
    · rw [index, ← anchorIndex]
      omega
    · rw [index]
      dsimp [offset]
      omega
  obtain ⟨b, a, d, hd, bound, run⟩ := window h1 h2 h3 h4 c start fourBlue
  have aBound : offset+a < 186 := by omega
  have dBound : d < 186 := by cases b <;> simp at bound <;> omega
  refine ⟨b, ⟨offset+a,aBound⟩, ⟨d,dBound⟩, hd, ?_, ?_⟩
  · dsimp
    omega
  · intro t ht
    simpa only [c, Nat.add_assoc] using run t ht

end OMA.R_Green14_W_3_14_R1_H2_R1