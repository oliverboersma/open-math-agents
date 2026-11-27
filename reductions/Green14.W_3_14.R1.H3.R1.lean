import OMAReductions.R_Green14_W_3_14_R1

/-!
A single 182-position window contains the relevant part of each outer center
gap. If the positions 87 through 94 are blue, a coloring without a blue
fourteen-term progression must have a first red between 95 and 100.
-/

namespace OMA.R_Green14_W_3_14_R1_H3_R1

def H1 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), p ∈ ([98] : List Nat) →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H2 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), p ∈ ([95,100] : List Nat) →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H3 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), p ∈ ([96,97] : List Nat) →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

def H4 : Prop :=
  ∀ (c : Nat → Bool) (p : Nat), p ∈ ([99] : List Nat) →
    c 86 = true → c p = true → (∀ q : Nat, 86 < q → q < p → c q = false) →
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b

theorem force_of_cases (h1 : H1) (h2 : H2) (h3 : H3) (h4 : H4)
    (c : Nat → Bool) (anchor : c 86 = true)
    (gap : ∀ p : Nat, 86 < p → p ≤ 94 → c p = false) :
    ∃ (b : Bool) (a d : Nat), 0 < d ∧ a + (if b then 2 else 13)*d < 182 ∧
      ∀ t : Fin 14, t.val ≤ (if b then 2 else 13) → c (a+t.val*d) = b := by
  classical
  by_cases allblue : ∀ p : Nat, 87 ≤ p → p ≤ 100 → c p = false
  · refine ⟨false, 87, 1, by omega, by decide, ?_⟩
    intro t h
    simpa using allblue (87+t.val) (by omega) (by omega)
  · push Not at allblue
    obtain ⟨z, hlo, hhi, hz⟩ := allblue
    let P := fun p : Nat => 87 ≤ p ∧ p ≤ 100 ∧ c p = true
    have hpExists : ∃ p, P p := ⟨z, hlo, hhi, Bool.ne_false_iff.mp hz⟩
    let p := Nat.find hpExists
    have hp : 87 ≤ p ∧ p ≤ 100 ∧ c p = true := Nat.find_spec hpExists
    have hBefore (q : Nat) (hlo : 86 < q) (hhi : q < p) : c q = false := by
      apply Bool.eq_false_iff.mpr
      intro hr
      exact Nat.find_min hpExists hhi ⟨by omega, by have := hp.2.1; omega, hr⟩
    have hpLow : 95 ≤ p := by
      by_contra! h
      have hb := gap p (by have := hp.1; omega) (by omega)
      rw [hb] at hp
      exact Bool.false_ne_true hp.2.2
    have hpHigh := hp.2.1
    rcases (show p = 95 ∨ p = 96 ∨ p = 97 ∨ p = 98 ∨ p = 99 ∨ p = 100 by omega) with
      h | h | h | h | h | h
    · exact h2 c p (by simp [h]) anchor hp.2.2 hBefore
    · exact h3 c p (by simp [h]) anchor hp.2.2 hBefore
    · exact h3 c p (by simp [h]) anchor hp.2.2 hBefore
    · exact h1 c p (by simp [h]) anchor hp.2.2 hBefore
    · exact h4 c p (by simp [h]) anchor hp.2.2 hBefore
    · exact h2 c p (by simp [h]) anchor hp.2.2 hBefore

theorem main : H1 → H2 → H3 → H4 → OMA.R_Green14_W_3_14_R1.H3 := by
  intro h1 h2 h3 h4 r j lo hi anchor gap
  let offset := 6-j.val
  have hoff : offset ≤ 2 := by dsimp [offset]; omega
  have he : offset+86 = 92-j.val := by dsimp [offset]; omega
  let c (p : Nat) := r (Fin.ofNat 186 (offset+p))
  have hAnchor : c 86 = true := by simpa only [c, he] using anchor
  have hGap (p : Nat) (hlo : 86 < p) (hhi : p ≤ 94) : c p = false := by
    have hpos : offset+p < 186 := by omega
    have hv : (Fin.ofNat 186 (offset+p)).val = offset+p := by
      simp [Nat.mod_eq_of_lt hpos]
    apply gap
    · rw [hv, ←he]
      omega
    · rw [hv]
      dsimp [offset]
      omega
  obtain ⟨b,a,d,hd,bound,run⟩ := force_of_cases h1 h2 h3 h4 c hAnchor hGap
  have ha : offset+a < 186 := by omega
  have hd' : d < 186 := by cases b <;> simp at bound <;> omega
  refine ⟨b,⟨offset+a,ha⟩,⟨d,hd'⟩,hd,?_,?_⟩
  · dsimp
    omega
  · intro t ht
    simpa only [c, Nat.add_assoc] using run t ht

end OMA.R_Green14_W_3_14_R1_H3_R1