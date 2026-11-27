import OMAReductions.R_Green14_W_3_13_R1

/-!
# Red radii in the two small central gaps

In the zero-gap case the first 159 sites suffice. In the two-blue case
the first 158 sites suffice, using only the blue site at distance two
to the right of the anchor. The points at equal distances to the left
and right of a red anchor cannot both be red. Recording the disjoint sets
of occupied left and right radii removes all triples with this midpoint
from the remaining tests.

The normalization into central gaps is from NickLeko's reduction in PR 3990.
Credit: @ZedingZhang.
-/

namespace OMA.R_Green14_W_3_13_R1_H1_R1

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

private lemma coordinates (c : ℕ → Bool) (p cap : ℕ) (anchor : c p = true)
    (mirror : ∀ d : ℕ, 0 < d → d ≤ p → d ≤ cap-p →
      c (p-d) = true → c (p+d) = true → False) :
    ∃ L R : Finset ℕ, L ⊆ Finset.Icc 1 p ∧ R ⊆ Finset.Icc 1 (cap-p) ∧
      Disjoint L R ∧ (∀ d ∈ R, c (p+d) = true) ∧
      ∀ x ≤ cap, (x = p ∨ (x < p ∧ p-x ∈ L) ∨ (p < x ∧ x-p ∈ R)) ↔ c x = true := by
  classical
  let L := (Finset.Icc 1 p).filter (fun d => c (p-d) = true)
  let R := (Finset.Icc 1 (cap-p)).filter (fun d => c (p+d) = true)
  refine ⟨L, R, Finset.filter_subset _ _, Finset.filter_subset _ _,
    Finset.disjoint_left.mpr ?_, ?_, ?_⟩
  · intro d hl hr
    obtain ⟨hl', cl⟩ := Finset.mem_filter.mp hl
    obtain ⟨hr', cr⟩ := Finset.mem_filter.mp hr
    exact mirror d (Finset.mem_Icc.mp hl').1 (Finset.mem_Icc.mp hl').2
      (Finset.mem_Icc.mp hr').2 cl cr
  · intro d h
    exact (Finset.mem_filter.mp h).2
  · intro x hx
    constructor
    · rintro (rfl | ⟨hl, h⟩ | ⟨hr, h⟩)
      · exact anchor
      · have cd := (Finset.mem_filter.mp h).2
        rwa [show p-(p-x)=x by omega] at cd
      · have cd := (Finset.mem_filter.mp h).2
        rwa [show p+(x-p)=x by omega] at cd
    · intro red
      rcases lt_trichotomy x p with hl | he | hr
      · refine Or.inr (Or.inl ⟨hl, ?_⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          by simpa only [show p-(p-x)=x by omega] using red⟩
      · exact Or.inl he
      · refine Or.inr (Or.inr ⟨hr, ?_⟩)
        exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩,
          by simpa only [show p+(x-p)=x by omega] using red⟩

private lemma shorter_window (c : ℕ → Bool) (p cap : ℕ) (small : cap < 160)
    (anchor : c p = true) (extra : Finset ℕ → Prop)
    (extract : ∀ R : Finset ℕ, (∀ d ∈ R, c (p+d) = true) → extra R)
    (window : ∀ L R : Finset ℕ, L ⊆ Finset.Icc 1 p → R ⊆ Finset.Icc 1 (cap-p) →
      Disjoint L R → extra R →
      let red (x : ℕ) := x = p ∨ (x < p ∧ p-x ∈ L) ∨ (p < x ∧ x-p ∈ R)
      (∀ a d : ℕ, 0 < d → a+2*d ≤ cap → a+d ≠ p →
        red a → red (a+d) → red (a+2*d) → False) →
      ∃ a d : ℕ, 0 < d ∧ a+12*d ≤ cap ∧ ∀ t : Fin 13, ¬red (a+t.val*d)) :
    ∃ (b : Bool) (a d : ℕ), 0 < d ∧ a + (if b then 2 else 12) * d < 160 ∧
      ∀ t : Fin 13, t.val ≤ (if b then 2 else 12) → c (a+t.val*d) = b := by
  by_contra none
  have noRed (a d : ℕ) (hd : 0 < d) (bound : a+2*d ≤ cap)
      (h₀ : c a = true) (h₁ : c (a+d) = true) (h₂ : c (a+2*d) = true) : False :=
    none (red_triple c a d hd (by omega) h₀ h₁ h₂)
  have mirror (d : ℕ) (hd : 0 < d) (hl : d ≤ p) (hr : d ≤ cap-p)
      (cl : c (p-d) = true) (cr : c (p+d) = true) : False := by
    exact noRed (p-d) d hd (by omega) cl
      (by simpa only [show p-d+d=p by omega] using anchor)
      (by simpa only [show p-d+2*d=p+d by omega] using cr)
  obtain ⟨L, R, hL, hR, hd, colors, rep⟩ := coordinates c p cap anchor mirror
  obtain ⟨a, d, hd', bound, run⟩ := window L R hL hR hd (extract R colors)
    (fun a d hp ha _ h₀ h₁ h₂ => noRed a d hp ha
      ((rep a (by omega)).mp h₀) ((rep (a+d) (by omega)).mp h₁) ((rep (a+2*d) ha).mp h₂))
  apply none
  refine ⟨false, a, d, hd', by change a+12*d < 160; omega, ?_⟩
  intro t ht
  change t.val ≤ 12 at ht
  have lim := Nat.mul_le_mul_right d ht
  apply Bool.eq_false_iff.mpr
  intro ht'
  exact run t ((rep (a+t.val*d) (by omega)).mpr ht')

/-- A red center in 159 positions forces a blue progression if the remaining red triples are excluded. -/
def H1 : Prop :=
  ∀ L R : Finset ℕ, L ⊆ Finset.Icc 1 79 → R ⊆ Finset.Icc 1 79 → Disjoint L R →
    let red (x : ℕ) := x = 79 ∨ (x < 79 ∧ 79-x ∈ L) ∨ (79 < x ∧ x-79 ∈ R)
    (∀ a d : ℕ, 0 < d → a+2*d ≤ 158 → a+d ≠ 79 →
      red a → red (a+d) → red (a+2*d) → False) →
    ∃ a d : ℕ, 0 < d ∧ a+12*d ≤ 158 ∧ ∀ t : Fin 13, ¬red (a+t.val*d)

/-- On 158 positions the right radius two is absent. -/
def H2 : Prop :=
  ∀ L R : Finset ℕ, L ⊆ Finset.Icc 1 78 → R ⊆ Finset.Icc 1 79 → Disjoint L R → 2 ∉ R →
    let red (x : ℕ) := x = 78 ∨ (x < 78 ∧ 78-x ∈ L) ∨ (78 < x ∧ x-78 ∈ R)
    (∀ a d : ℕ, 0 < d → a+2*d ≤ 157 → a+d ≠ 78 →
      red a → red (a+d) → red (a+2*d) → False) →
    ∃ a d : ℕ, 0 < d ∧ a+12*d ≤ 157 ∧ ∀ t : Fin 13, ¬red (a+t.val*d)

theorem main : H1 → H2 → OMA.R_Green14_W_3_13_R1.H1 := by
  intro middle neighbor r j _ high hred hblue
  let c (n : ℕ) := r (Fin.ofNat 160 n)
  have anchor : c (79-j.val) = true := hred
  apply finite_progression r
  by_cases hj : j.val = 0
  · have red79 : c 79 = true := by simpa only [hj, Nat.sub_zero] using anchor
    exact shorter_window c 79 158 (by decide) red79 (fun _ => True)
      (fun _ _ => trivial) (fun L R hl hr hd _ => middle L R hl hr hd)
  · have hj' : j.val = 1 := by omega
    have red78 : c 78 = true := by simpa [hj'] using anchor
    have blue80 : c 80 = false := by
      apply hblue (Fin.ofNat 160 80)
      · simp [hj']
      · simp [hj']
    apply shorter_window c 78 157 (by decide) red78 (fun R => 2 ∉ R) ?_ neighbor
    intro R colors hmem
    have impossible : c 80 = true := colors 2 hmem
    rw [blue80] at impossible
    cases impossible

end OMA.R_Green14_W_3_13_R1_H1_R1
