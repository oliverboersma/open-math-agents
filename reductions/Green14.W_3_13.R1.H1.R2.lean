import OMAReductions.R_Green14_W_3_13_R1

/-!
# The two central patterns on 158 sites

For NickLeko's central-gap reduction of the upper bound W(3,13) ≤ 160,
restrict to the sites numbered 0 through 157. In both hypotheses `S` is
the set of red sites. An avoiding coloring has no red three-term
progression and every thirteen-term progression meets red.

The reflection and window argument is due to @anmolspace with Codex in
PR #5642. Its centered 159-site restriction builds on ZedingZhang's
reduction #5287. Ahmed, Kullmann and Snevily established the numerical value.
-/

namespace OMA.R_Green14_W_3_13_R1_H1_R2

/-- The red site 78 is followed by the two blue sites 79 and 80. -/
def H1 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 78 → ¬S 79 → ¬S 80 → False

/-- The three sites 76, 78, and 79 are all red. -/
def H2 : Prop :=
  ∀ (S : Nat → Prop), (∀ x, S x → x ≤ 157) →
    (∀ a d, 0 < d → S a → S (a+d) → S (a+2*d) → False) →
    (∀ a d, 0 < d → a+12*d < 158 → ∃ t ≤ 12, S (a+t*d)) →
    S 76 → S 78 → S 79 → False

theorem main : H1 → H2 → OMA.R_Green14_W_3_13_R1.H1 := by
  intro twoBlue threeRed
  let NoTriple (R : Nat → Prop) :=
    ∀ a d, 0 < d → R a → R (a+d) → R (a+2*d) → False

  let Goal (r : Fin 160 → Bool) :=
    ∃ (b : Bool) (a d : Fin 160), 0 < d.val ∧ a.val + (if b then 2 else 12)*d.val < 160 ∧
      ∀ t : Fin 13, t.val ≤ (if b then 2 else 12) → r (Fin.ofNat 160 (a.val + t.val*d.val)) = b


  let R (o : Nat) (r : Fin 160 → Bool) (x : Nat) : Prop :=
    o ≤ x ∧ x < o + 160 ∧ r (Fin.ofNat 160 (x - o)) = true

  have noTriple_of {r : Fin 160 → Bool} (hn : ¬ Goal r) (o : Nat) :
      NoTriple (R o r) := by
    intro a d hd h₀ h₁ h₂
    obtain ⟨ha, _, h₀⟩ := h₀
    obtain ⟨_, _, h₁⟩ := h₁
    obtain ⟨_, he, h₂⟩ := h₂
    apply hn
    have hend : a - o + 2 * d < 160 := by omega
    refine ⟨true, ⟨a - o, by omega⟩, ⟨d, by omega⟩, hd, hend, ?_⟩
    intro t ht
    change t.val ≤ 2 at ht
    change r (Fin.ofNat 160 (a - o + t.val * d)) = true
    rcases (show t.val = 0 ∨ t.val = 1 ∨ t.val = 2 by omega) with hz | hu | ht
    · simpa only [hz, Nat.zero_mul, Nat.add_zero] using h₀
    · simpa only [hu, Nat.one_mul, show a + d - o = a - o + d by omega] using h₁
    · simpa only [ht, show a + 2 * d - o = a - o + 2 * d by omega] using h₂

  have red_hits {r : Fin 160 → Bool} (hn : ¬ Goal r) {o a d : Nat}
      (ha : o ≤ a) (hd : 0 < d) (he : a + 12 * d < o + 160) :
      ∃ t ≤ 12, R o r (a + t * d) := by
    apply Classical.byContradiction
    intro h
    apply hn
    have hend : a - o + 12 * d < 160 := by omega
    refine ⟨false, ⟨a - o, by omega⟩, ⟨d, by omega⟩, hd, hend, ?_⟩
    intro t ht
    change t.val ≤ 12 at ht
    change r (Fin.ofNat 160 (a - o + t.val * d)) = false
    cases hv : r (Fin.ofNat 160 (a - o + t.val * d)) with
    | false => rfl
    | true =>
      exfalso
      apply h
      have htd : t.val * d ≤ 12 * d := Nat.mul_le_mul_right d ht
      refine ⟨t.val, ht, by omega, by omega, ?_⟩
      simpa only [show a + t.val * d - o = a - o + t.val * d by omega] using hv

  -- The centered 159-site restriction is the observation of ZedingZhang in PR 5287.
  let LineMeets (n : Nat) (S : Nat → Prop) : Prop :=
    ∀ a d, 0 < d → a + 12*d < n → ∃ t ≤ 12, S (a+t*d)

  let Flip159 (S : Nat → Prop) (x : Nat) : Prop := x ≤ 158 ∧ S (158-x)

  have flip_noTriple {S : Nat → Prop} (hn : NoTriple S) :
      NoTriple (Flip159 S) := by
    intro a d hd h₀ h₁ h₂
    obtain ⟨_,h₀⟩ := h₀
    obtain ⟨_,h₁⟩ := h₁
    obtain ⟨he,h₂⟩ := h₂
    apply hn (158-(a+2*d)) d hd h₂
    · simpa only [show 158-(a+2*d)+d = 158-(a+d) by omega] using h₁
    · simpa only [show 158-(a+2*d)+2*d = 158-a by omega] using h₀

  have flip_lineMeets {S : Nat → Prop} (hh : LineMeets 159 S) :
      LineMeets 159 (Flip159 S) := by
    intro a d hd he
    obtain ⟨t,ht,hr⟩ := hh (158-(a+12*d)) d hd (by omega)
    have hmul := Nat.mul_le_mul_right d ht
    refine ⟨12-t, by omega, ?_, ?_⟩
    · rw [Nat.sub_mul]
      omega
    · have heq : 158-(a+(12-t)*d) = 158-(a+12*d)+t*d := by
        rw [Nat.sub_mul]
        omega
      exact heq.symm ▸ hr

  let NearCase (S : Nat → Prop) : Prop :=
    (∀ x, S x → x ≤ 157) ∧ NoTriple S ∧ LineMeets 158 S ∧ S 78 ∧
      ((¬S 79 ∧ ¬S 80) ∨ (S 76 ∧ S 79))

  have shiftWindow {T : Nat → Prop} (ht : NoTriple T)
      (hm : LineMeets 159 T) (hr : T 79)
      (shape : (¬T 80 ∧ ¬T 81) ∨ (T 77 ∧ T 80)) : ∃ S, NearCase S := by
    let S := fun x => x ≤ 157 ∧ T (x+1)
    refine ⟨S, fun _ h => h.1, ?_, ?_, ⟨by decide, hr⟩, ?_⟩
    · intro a d hd h₀ h₁ h₂
      apply ht (a+1) d hd h₀.2
      · simpa only [show a+1+d=(a+d)+1 by omega] using h₁.2
      · simpa only [show a+1+2*d=(a+2*d)+1 by omega] using h₂.2
    · intro a d hd he
      obtain ⟨t, h, hred⟩ := hm (a+1) d hd (by omega)
      have htd := Nat.mul_le_mul_right d h
      exact ⟨t, h, by omega, by simpa only [show a+1+t*d = a+t*d+1 by omega] using hred⟩
    · rcases shape with ⟨h₁,h₂⟩|⟨h₁,h₂⟩
      · exact Or.inl ⟨fun h => h₁ h.2, fun h => h₂ h.2⟩
      · exact Or.inr ⟨⟨by decide,h₁⟩,⟨by decide,h₂⟩⟩

  have windowZero {r : Fin 160 → Bool} (hn : ¬Goal r)
      (ha : r (Fin.ofNat 160 79) = true) : ∃ S, NearCase S := by
    let T := fun x => x ≤ 158 ∧ R 0 r x
    have ht : NoTriple T := fun a d hd h₀ h₁ h₂ => noTriple_of hn 0 a d hd h₀.2 h₁.2 h₂.2
    have hm : LineMeets 159 T := by
      intro a d hd he
      obtain ⟨t,h,hr⟩ := red_hits hn (o:=0) (a:=a) (by omega) hd (by omega)
      have htd := Nat.mul_le_mul_right d h
      exact ⟨t,h,by omega,hr⟩
    have hc : T 79 := ⟨by decide,by decide,by decide,ha⟩
    have flip := shiftWindow (T:=Flip159 T) (flip_noTriple ht) (flip_lineMeets hm)
      (show Flip159 T 79 from ⟨by decide,hc⟩)
    by_cases h80 : T 80
    · have h78 : ¬T 78 := fun h => ht 78 1 (by decide) h hc h80
      by_cases h77 : T 77
      · exact shiftWindow ht hm hc (Or.inr ⟨h77,h80⟩)
      · exact flip (Or.inl ⟨fun h => h78 h.2, fun h => h77 h.2⟩)
    · by_cases h81 : T 81
      · have h77 : ¬T 77 := fun h => ht 77 2 (by decide) h hc h81
        by_cases h78 : T 78
        · exact flip (Or.inr ⟨⟨by decide,h81⟩,⟨by decide,h78⟩⟩)
        · exact flip (Or.inl ⟨fun h => h78 h.2, fun h => h77 h.2⟩)
      · exact shiftWindow ht hm hc (Or.inl ⟨h80,h81⟩)

  have windowOne {r : Fin 160 → Bool} (hn : ¬Goal r)
      (ha : r (Fin.ofNat 160 78) = true)
      (hb : ∀ i : Fin 160, 78 < i.val → i.val < 81 → r i = false) : ∃ S, NearCase S := by
    let S := fun x => x ≤ 157 ∧ R 0 r x
    refine ⟨S, fun _ h => h.1, ?_, ?_, ⟨by decide,by decide,by decide,ha⟩, Or.inl ⟨?_,?_⟩⟩
    · exact fun a d hd h₀ h₁ h₂ => noTriple_of hn 0 a d hd h₀.2 h₁.2 h₂.2
    · intro a d hd he
      obtain ⟨t,h,hr⟩ := red_hits hn (o:=0) (a:=a) (by omega) hd (by omega)
      have htd := Nat.mul_le_mul_right d h
      exact ⟨t,h,by omega,hr⟩
    · intro h
      have he : r (Fin.ofNat 160 79) = true := h.2.2.2
      rw [hb (Fin.ofNat 160 79) (by decide) (by decide)] at he
      cases he
    · intro h
      have he : r (Fin.ofNat 160 80) = true := h.2.2.2
      rw [hb (Fin.ofNat 160 80) (by decide) (by decide)] at he
      cases he
  have impossible {S : Nat → Prop} (h : NearCase S) : False := by
    obtain ⟨bound, triples, meets, center, shape⟩ := h
    rcases shape with ⟨h79,h80⟩ | ⟨h76,h79⟩
    · exact twoBlue S bound triples meets center h79 h80
    · exact threeRed S bound triples meets h76 center h79
  intro r j _ hhi hr hb
  change Goal r
  apply Classical.byContradiction
  intro hn
  rcases (show j.val = 0 ∨ j.val = 1 by omega) with hj | hj
  · obtain ⟨S,h⟩ := windowZero hn (by simpa only [hj] using hr)
    exact impossible h
  · obtain ⟨S,h⟩ := windowOne hn (by simpa only [hj] using hr) (by simpa only [hj] using hb)
    exact impossible h

end OMA.R_Green14_W_3_13_R1_H1_R2
