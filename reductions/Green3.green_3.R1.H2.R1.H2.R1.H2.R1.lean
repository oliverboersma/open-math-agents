import OMAReductions.R_Green3_green_3_R1_H2_R1_H2_R1

/-! Three disjoint translates of truncated prefixes give a strict cardinality
bound unless specific differences are already realized before the threshold.
This removes all configurations with minimum at most four and shows that
a counterexample must miss every integer from 2a−4 through 2a+2.
Original Lean proof by @Deldor14. -/

namespace OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1

open Finset

private lemma excluded_near_member (T : Finset ℕ)
    (hs : ∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l)
    {c d x : ℕ} (hc : c ∈ T) (hx : x ∈ T) (hlo : c ≤ d+1) (hhi : d ≤ c+2) : x+d ∉ T := by
  intro he
  have h := hs x hx c hc (x+d) he
  omega

/-- Pack the three prefixes after translating them by d+e, e and zero. -/
def H1 : Prop := ∀ (T : Finset ℕ) (a u d e : ℕ), (∀ x ∈ T, a ≤ x) → u ∈ T →
    e ≤ a → d+e < 2*a → (∀ x ∈ T, x ≤ u → x+d ∉ T) →
    (∀ x ∈ T, x < u+a → x+e ∉ T) → (∀ x ∈ T, x ≤ u → x+(d+e) ∉ T) →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

/-- Remaining configurations have large minimum, an empty interval around twice
that minimum, and mandatory local differences for every admissible pair of offsets. -/
def H2 : Prop := ∀ (T : Finset ℕ) (a u : ℕ), a ∈ T → u ∈ T → u+2*a ∈ T →
    (∀ i ∈ T, a ≤ i ∧ i ≤ u+2*a) →
    (∀ i ∈ T, ∀ j ∈ T, ∀ l ∈ T, l+1 < i+j ∨ i+j+2 < l) →
    5 ≤ a → u+a+1 < 3*T.card → (∀ x ∈ T, x+4 < 2*a ∨ 2*a+2 < x) →
    (∀ d e : ℕ, e ≤ a → d+e < 2*a →
      (∀ x ∈ T, x ≤ u → x+d ∉ T) → (∀ x ∈ T, x < u+a → x+e ∉ T) →
        ∃ x ∈ T, x ≤ u ∧ x+(d+e) ∈ T) →
    (T.filter (· < u)).card + (T.filter (· < u+a)).card +
      (T.filter (· < u+2*a)).card < u+a

theorem main : H1 → H2 → OMA.R_Green3_green_3_R1_H2_R1_H2_R1.H2 := by
  classical
  intro pack tail T a ha hmin hsep u hu hu2 _hdense
  let V := T.filter (· ≤ u+2*a)
  have haV : a ∈ V := mem_filter.mpr ⟨ha,by omega⟩
  have huV : u ∈ V := mem_filter.mpr ⟨hu,by omega⟩
  have hu2V : u+2*a ∈ V := mem_filter.mpr ⟨hu2,le_rfl⟩
  have hbounds (x : ℕ) (hx : x ∈ V) : a ≤ x ∧ x ≤ u+2*a :=
    ⟨hmin x (mem_filter.mp hx).1,(mem_filter.mp hx).2⟩
  have hs (i : ℕ) (hi : i ∈ V) (j : ℕ) (hj : j ∈ V) (l : ℕ) (hl : l ∈ V) :
      l+1 < i+j ∨ i+j+2 < l := hsep i (mem_filter.mp hi).1 j (mem_filter.mp hj).1 l (mem_filter.mp hl).1
  have hh (n : ℕ) (hn : n ≤ u+2*a) : V.filter (· < n) = T.filter (· < n) := by
    ext x
    simp only [V,mem_filter]
    constructor
    · rintro ⟨⟨hx,_⟩,hl⟩; exact ⟨hx,hl⟩
    · rintro ⟨hx,hl⟩; exact ⟨⟨hx,by omega⟩,hl⟩
  rw [←hh u (by omega),←hh (u+a) (by omega),←hh (u+2*a) le_rfl]
  by_contra! hfail
  have hsize : u+a+1 < 3*V.card := by
    have hbound (n : ℕ) (hn : n ≤ u+2*a) : (V.filter (· < n)).card < V.card :=
      card_lt_card (filter_ssubset.mpr ⟨u+2*a,hu2V,by omega⟩)
    have h₁ := hbound u (by omega)
    have h₂ := hbound (u+a) (by omega)
    have h₃ := hbound (u+2*a) le_rfl
    omega
  have hhit (d e : ℕ) (he : e ≤ a) (hsum : d+e < 2*a)
      (hD : ∀ x ∈ V, x ≤ u → x+d ∉ V) (hE : ∀ x ∈ V, x < u+a → x+e ∉ V) :
      ∃ x ∈ V, x ≤ u ∧ x+(d+e) ∈ V := by
    by_contra! h
    exact (not_lt_of_ge hfail) (pack V a u d e (fun x hx => (hbounds x hx).1) huV he hsum hD hE h)
  have hapos : 2 ≤ a := by have := hs a haV a haV a haV; omega
  let b := a-1
  have hba : b+1 = a := Nat.sub_add_cancel (by omega)
  have hb (x : ℕ) (hx : x ∈ V) : x+b ∉ V := excluded_near_member V hs haV hx (by omega) (by omega)
  obtain ⟨z,hz,_,hsum⟩ := hhit b b (by omega) (by omega) (fun x hx _ => hb x hx) (fun x hx _ => hb x hx)
  have ha5 : 5 ≤ a := by
    by_contra! hl
    exact excluded_near_member V hs haV hz (by omega) (by omega) hsum
  have hgap (x : ℕ) (hx : x ∈ V) : x+4 < 2*a ∨ 2*a+2 < x := by
    by_contra! h
    have hbefore := hs a haV a haV x hx
    exact excluded_near_member V hs hx hz (by omega) (by omega) hsum
  exact (not_lt_of_ge hfail) (tail V a u haV huV hu2V hbounds hs ha5 hsize hgap hhit)

end OMA.R_Green3_green_3_R1_H2_R1_H2_R1_H2_R1
